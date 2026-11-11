"""Consolidate all unit reviews and admit only evidence-backed completions."""

from __future__ import annotations

import copy
import hashlib
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REVIEW_FILES = ("contracts-scalar-main-review.json", "radial-review.json",
                "geometry-review.json", "analysis-nonlinear-review.json")


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    metadata = read(HERE / "source-snapshot.json")
    builds = read(HERE / "build-results.json")
    declarations = read(HERE / "declaration-check.json")
    assert builds.get("finished_at_utc") and builds["axiom_audit"]["exit_code"] == 0
    assert declarations["exit_code"] == 0 and declarations["owner_unsafe_audit_passed"]
    assert declarations["build_report_sha256"] == digest(HERE / "build-results.json")
    tasks = {t["id"]: t for t in read(ROOT / "blueprint/refinement/manifest.json")["tasks"]}
    reviews = {}
    sources = {}
    supported = set(declarations["supported_candidate_ids"])
    for name in REVIEW_FILES:
        path = HERE / name
        sources[path.relative_to(ROOT).as_posix()] = digest(path)
        for original in read(path)["reviews"]:
            record = copy.deepcopy(original)
            ident = record["id"]
            assert ident not in reviews, ident
            task = tasks[ident]
            record["title"] = task["title"]
            assert record["statement"] == task["statement"], ident
            criteria = record["acceptance_coverage"]
            if isinstance(criteria, dict):
                criteria = [{"criterion": key, **value} for key, value in sorted(criteria.items())]
            for index, item in enumerate(criteria, 1):
                item["criterion"] = item.get("criterion", item.get("id"))
                assert item["criterion"] == f"acceptance.{index:02}"
                assert item["text"] == task["acceptance"][index - 1]
                if "evidence" not in item:
                    names = set(item.get("declarations", []))
                    item["evidence"] = [{"file": e["file"], "declarations": [n for n in e["declarations"] if n in names]}
                                        for e in record["evidence"] if any(n in names for n in e["declarations"])]
                if item["status"] == "missing":
                    item["status"] = "uncovered"
            record["acceptance_coverage"] = criteria
            record["statement_coverage"] = {
                "status": "covered" if record["status"] == "complete" else "partial" if record["evidence"] else "uncovered",
                "evidence": [{"file": e["file"], "declarations": e["declarations"]} for e in record["evidence"]],
                "correspondence": record["rationale"],
            }
            record["review_source"] = path.relative_to(ROOT).as_posix()
            for evidence in record["evidence"]:
                assert record["source_sha256"][evidence["file"]] == metadata["files"][evidence["file"]], ident
            if record["status"] == "complete" and ident not in supported:
                failed = [e["file"] for e in record["evidence"]
                          if builds["modules"].get(e["file"][:-5].replace("/", "."), {}).get("status") != "passed"]
                assert failed, f"A successful module's proposed unit unexpectedly failed declaration validation: {ident}"
                record["candidate_status"] = "complete"
                record["status"] = "partial"
                record["remaining"] = record["remaining"] + ["支持模块尚未在冻结源码中编译通过：" + ", ".join(failed)]
                record["rationale"] += " 本轮源码编译未通过，不能计入完整完成。"
                record["statement_coverage"]["status"] = "partial"
                record["build_status"] = "failed_support_not_counted"
            elif record["status"] == "complete":
                record["build_status"] = "isolated_build_owner_axiom_unsafe_and_declaration_checks_passed"
            else:
                record["build_status"] = "not_a_complete_unit"
            reviews[ident] = record
    assert set(reviews) == set(tasks), (set(tasks) - set(reviews), set(reviews) - set(tasks))
    results = {
        "schema_version": 1, "captured_at_utc": metadata["captured_at_utc"],
        "registered_at_utc": datetime.now(timezone.utc).isoformat(),
        "task_contracts": metadata["task_contracts"],
        "review_sources": sources,
        "verification": {
            key: (HERE / name).relative_to(ROOT).as_posix()
            for key, name in [("snapshot_metadata", "source-snapshot.json"), ("snapshot_archive", "source-snapshot.zip"),
                              ("build_report", "build-results.json"), ("declaration_report", "declaration-check.json")]
        },
        "reviews": [reviews[key] for key in tasks],
        "counts": dict(Counter(r["status"] for r in reviews.values())),
        "limits": ["计数对应冻结源码和原任务完整目标，不包含之后的并行修改。",
                   "局部/通用条件定理完成不证明输入结构非空或完整MAIN。",
                   "原58个里程碑状态不因本轮子任务登记自动升级。",
                   "同一已证定理可支持多个任务，任务数不是独立定理数或数学工作量百分比。"],
    }
    for key, relative in list(results["verification"].items()):
        results["verification"][key + "_sha256"] = digest(ROOT / relative)
    temporary = HERE / "progress.json.tmp"
    temporary.write_text(json.dumps(results, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(HERE / "progress.json")
    print({"reviewed": len(reviews), "counts": results["counts"]})


if __name__ == "__main__":
    main()
