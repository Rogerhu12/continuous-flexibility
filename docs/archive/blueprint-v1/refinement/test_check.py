"""Regression checks for lost obligations and unsupported completion claims."""

from __future__ import annotations

import copy
import unittest
from unittest.mock import patch

import check


class RefinementValidationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.base = check.read(check.BASE)
        cls.manifest = check.make_manifest(
            cls.base, [check.read(p) for p in sorted(check.PARTS.glob("*.json"))]
        )

    def setUp(self) -> None:
        self.data = copy.deepcopy(self.manifest)
        self.task = next(t for t in self.data["tasks"] if t["status"] == "planned")

    def rejects(self, text: str) -> None:
        with self.assertRaisesRegex(ValueError, text):
            check.validate(self.data, self.base)

    def test_complete_plan_preserves_main_scope(self) -> None:
        result = check.validate(self.data, self.base)
        self.assertTrue(result["dag_valid"])
        self.assertTrue(result["main_closure_preserved"])
        self.assertEqual(result["retained_complete_tasks"], 3)
        expected = sum(r["status"] == "complete" for r in check.read(check.PROGRESS)["reviews"]) if check.PROGRESS.exists() else 3
        self.assertEqual(result["complete_tasks"], expected)
        self.assertEqual(result["new_completion_claims"], expected - 3)
        self.assertEqual(result["complete_tasks"] + result["partial_tasks"] + result["planned_tasks"], 514)

    def test_missing_acceptance_coverage_is_rejected(self) -> None:
        self.data["milestones"][0]["coverage"][1]["tasks"] = []
        self.rejects("coverage")

    def test_changed_original_statement_is_rejected(self) -> None:
        self.data["milestones"][0]["contract"]["statement"] = "A weaker theorem"
        self.rejects("Original statement")

    def test_unsupported_completion_is_rejected(self) -> None:
        self.task["status"] = "retained_proof"
        self.task["estimated_new_lean_lines"] = [0, 0]
        self.rejects("Unsupported completion")

    def test_lost_original_dependency_is_rejected(self) -> None:
        item = next(t for t in self.data["tasks"] if t["upstream_milestones"])
        item["upstream_milestones"] = []
        self.rejects("Lost original dependency")

    def test_dangling_dependency_is_rejected(self) -> None:
        self.task["depends_on"].append("MISSING.01")
        self.rejects("Dangling")

    def test_local_cycle_is_rejected(self) -> None:
        parent = next(m for m in self.data["milestones"] if len(m["tasks"]) > 1)
        lookup = {t["id"]: t for t in self.data["tasks"]}
        lookup[parent["tasks"][0]]["depends_on"].append(parent["completion_task"])
        self.rejects("cycle")

    def test_extra_milestone_cycle_is_rejected(self) -> None:
        item = next(t for t in self.data["tasks"] if t["parent"] == "H01")
        item["extra_dependencies"] = [{"milestone": "MAIN", "reason": "Deliberate cycle"}]
        self.rejects("cycle")

    def test_assembly_cannot_skip_children(self) -> None:
        parent = next(m for m in self.data["milestones"] if len(m["tasks"]) > 1)
        item = next(t for t in self.data["tasks"] if t["id"] == parent["completion_task"])
        item["depends_on"] = []
        self.rejects("assembly omits")

    def test_work_above_resplit_threshold_is_rejected(self) -> None:
        self.task["estimated_new_lean_lines"] = [200, 801]
        self.rejects("resplitting")

    def test_main_task_cannot_become_optional(self) -> None:
        self.task["required_for_main"] = False
        self.rejects("Main scope changed")

    def test_new_dependency_needs_reason(self) -> None:
        self.task["extra_dependencies"] = [{"milestone": "S01", "reason": ""}]
        self.rejects("Invalid extra dependency")


@unittest.skipUnless(check.PROGRESS.exists(), "No evidence-backed progress registry yet")
class CompletionEvidenceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.base = check.read(check.BASE)
        self.data = check.make_manifest(self.base, [check.read(p) for p in sorted(check.PARTS.glob("*.json"))])
        self.progress = copy.deepcopy(check.read(check.PROGRESS))
        self.item = next(r for r in self.progress["reviews"] if r["status"] == "complete")

    def rejects_registry(self, pattern: str) -> None:
        original_read = check.read

        def altered(path):
            return self.progress if path == check.PROGRESS else original_read(path)

        with patch.object(check, "read", side_effect=altered):
            with self.assertRaisesRegex(ValueError, pattern):
                check.validate(self.data, self.base)

    def rejects_report(self, key: str, mutate, pattern: str) -> None:
        original_read = check.read
        target = check.ROOT / self.progress["verification"][key]
        report = copy.deepcopy(original_read(target))
        mutate(report)

        def altered(path):
            return report if path.resolve() == target.resolve() else original_read(path)

        with patch.object(check, "read", side_effect=altered):
            with self.assertRaisesRegex(ValueError, pattern):
                check.validate(self.data, self.base)

    def test_complete_requires_full_statement_correspondence(self) -> None:
        self.item.pop("statement_coverage")
        self.rejects_registry("Full statement not covered")

    def test_complete_cannot_leave_acceptance_uncovered(self) -> None:
        self.item["acceptance_coverage"][0]["status"] = "partial"
        self.rejects_registry("Acceptance not fully covered")

    def test_complete_cannot_keep_missing_obligations(self) -> None:
        self.item["remaining"] = ["An unproved conclusion"]
        self.rejects_registry("Complete task has missing")

    def test_every_task_must_be_reviewed(self) -> None:
        self.progress["reviews"].pop()
        self.rejects_registry("every task exactly once")

    def test_evidence_source_hash_must_match(self) -> None:
        path = self.item["evidence"][0]["file"]
        self.item["source_sha256"][path] = "0" * 64
        self.rejects_registry("Evidence source hash differs")

    def test_failed_module_cannot_support_completion(self) -> None:
        module = self.item["evidence"][0]["file"][:-5].replace("/", ".")
        self.rejects_report("build_report", lambda r: r["modules"][module].update(status="failed", exit_code=1), "not built/audited")

    def test_module_must_be_in_owner_audit(self) -> None:
        module = self.item["evidence"][0]["file"][:-5].replace("/", ".")
        self.rejects_report("build_report", lambda r: r["axiom_audit"]["modules"].remove(module), "not built/audited")

    def test_declaration_must_resolve(self) -> None:
        name = self.item["evidence"][0]["declarations"][0]
        self.rejects_report("declaration_report", lambda r: r["resolved_names"].remove(name), "Unresolved declaration")

    def test_declaration_owner_must_be_the_claimed_module(self) -> None:
        name = self.item["evidence"][0]["declarations"][0]
        self.rejects_report("declaration_report", lambda r: r["declaration_owners"].update({name: "Mathlib.Other"}), "Declaration owner differs")

    def test_declaration_report_cannot_use_another_snapshot(self) -> None:
        self.rejects_report("declaration_report", lambda r: r.update(snapshot="another-snapshot"), "another frozen build")

    def test_declaration_report_cannot_use_other_oleans(self) -> None:
        module = self.item["evidence"][0]["file"][:-5].replace("/", ".")
        self.rejects_report("declaration_report", lambda r: r["module_olean_sha256"].update({module: "0" * 64}), "Declaration artifacts differ")

    def test_acceptance_cannot_reference_an_unverified_constant(self) -> None:
        self.item["acceptance_coverage"][0]["evidence"] = [{"file": self.item["evidence"][0]["file"], "declarations": ["Missing.theorem"]}]
        self.rejects_registry("unverified evidence")


if __name__ == "__main__":
    unittest.main()
