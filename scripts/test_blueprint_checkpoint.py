"""Regressions for keeping audited proof sources separate from parallel drafts."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_blueprint as bp


class CheckpointScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.patch = patch.object(bp, "ROOT", self.root)
        self.patch.start()
        for directory in ("ContinuousFlexibility", "coordination"):
            (self.root / directory).mkdir()
        texts = {
            "ContinuousFlexibility.lean": "import ContinuousFlexibility.Stable\n",
            "AxiomAudit.lean": "import ContinuousFlexibility\n",
            "ContinuousFlexibility/Stable.lean": "-- a frozen source fixture\n",
            "ContinuousFlexibility/Draft.lean": "-- a live, unverified source fixture\n",
        }
        for name, text in texts.items():
            (self.root / name).write_text(text, encoding="utf-8")
        self.checkpoint = {
            "build": {"terminal_exit_code": 0, "warnings": 0,
                      "audit_declarations": 2, "audit_theorems": 1},
            "toolchain": "pinned-lean", "mathlib_commit": "pinned-mathlib",
            "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"],
            "sources": {name: {"sha256": hashlib.sha256((self.root / name).read_bytes()).hexdigest()}
                        for name in texts if not name.endswith("Draft.lean")},
        }
        self.data = {"proof_checkpoint": "coordination/checkpoint.json",
                     "lean_toolchain": "pinned-lean", "mathlib_commit": "pinned-mathlib"}
        self.registry = {"workers": [{"worker": "draft-owner",
                                      "scope": ["ContinuousFlexibility/Draft.lean"]}]}
        self.write_metadata()

    def tearDown(self):
        self.patch.stop()
        self.temp.cleanup()

    def write_metadata(self):
        (self.root / "coordination/checkpoint.json").write_text(json.dumps(self.checkpoint), encoding="utf-8")
        (self.root / "coordination/active-workers.json").write_text(json.dumps(self.registry), encoding="utf-8")

    def test_owned_draft_is_explicitly_excluded(self):
        included, report = bp.evidence_sources(self.data)
        self.assertEqual([p.name for p in included], ["Stable.lean"])
        self.assertEqual(report["excluded_unverified_sources"], ["ContinuousFlexibility/Draft.lean"])

    def test_hash_drift_is_rejected(self):
        (self.root / "ContinuousFlexibility/Stable.lean").write_text("changed", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "Audited source changed"):
            bp.evidence_sources(self.data)

    def test_root_hash_is_bound(self):
        with (self.root / "ContinuousFlexibility.lean").open("a", encoding="utf-8") as handle:
            handle.write("-- changed imports\n")
        with self.assertRaisesRegex(ValueError, "Audited source changed"):
            bp.evidence_sources(self.data)

    def test_unowned_draft_is_rejected(self):
        self.registry["workers"] = []
        self.write_metadata()
        with self.assertRaisesRegex(ValueError, "unique registered owner"):
            bp.evidence_sources(self.data)

    def test_ambiguous_owner_is_rejected(self):
        self.registry["workers"].append({"worker": "other", "scope": ["ContinuousFlexibility/"]})
        self.write_metadata()
        with self.assertRaisesRegex(ValueError, "unique registered owner"):
            bp.evidence_sources(self.data)

    def test_frozen_delivery_outside_current_checkpoint_remains_owned(self):
        self.registry["workers"] = [{"worker": "previous-owner", "scope": [],
                                    "frozen_deliveries": ["ContinuousFlexibility/Draft.lean"]}]
        self.write_metadata()
        _, report = bp.evidence_sources(self.data)
        self.assertEqual(report["excluded_unverified_sources"], ["ContinuousFlexibility/Draft.lean"])

    def test_vacuous_audit_is_rejected(self):
        self.checkpoint["build"]["audit_theorems"] = 0
        self.write_metadata()
        with self.assertRaisesRegex(ValueError, "nonvacuous owner audit"):
            bp.evidence_sources(self.data)

    def test_full_workspace_cannot_skip_unimported_draft(self):
        with self.assertRaisesRegex(ValueError, "absent from audit entry point"):
            bp.evidence_sources(self.data, full_workspace=True)

    def test_checkpoint_must_bind_every_root_import(self):
        del self.checkpoint["sources"]["ContinuousFlexibility/Stable.lean"]
        self.write_metadata()
        with self.assertRaisesRegex(ValueError, "omits an imported project module"):
            bp.evidence_sources(self.data)

    def test_unexpected_axiom_allowance_is_rejected(self):
        self.checkpoint["axiom_allowlist"].append("sorryAx")
        self.write_metadata()
        with self.assertRaisesRegex(ValueError, "unexpected axiom"):
            bp.evidence_sources(self.data)

    def test_failed_build_cannot_be_used_as_evidence(self):
        self.checkpoint["build"]["terminal_exit_code"] = 1
        self.write_metadata()
        with self.assertRaisesRegex(ValueError, "successful zero-warning build"):
            bp.evidence_sources(self.data)


if __name__ == "__main__":
    unittest.main()
