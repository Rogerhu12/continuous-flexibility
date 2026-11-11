"""Validate and render the fine-grained proof plan, without changing Lean files.

The original manifest remains the authority for milestone statements and proof
status. This program checks planning data, not mathematical correctness.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import zipfile
from collections import Counter
from datetime import datetime, timedelta, timezone
from graphlib import CycleError, TopologicalSorter
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = ROOT / "blueprint/manifest.json"
PARTS = HERE / "parts"
PROGRESS = HERE / "audit/progress.json"
GROUPS = {
    "Contracts": "目标与接口", "Scalar": "标量方程", "Radial": "径向参考",
    "Analysis": "分析基础与加权空间", "Nonlinear": "非线性存在性",
    "Geometry": "几何闭合", "Main": "主定理组装", "Extensions": "加强旁支",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def canonical_digest(value: object) -> str:
    return hashlib.sha256(json.dumps(value, ensure_ascii=False,
                                    sort_keys=True).encode("utf-8")).hexdigest()


def task_digest(task: dict) -> str:
    return canonical_digest({k: task[k] for k in ("id", "title", "statement", "acceptance")})


def checked_file(relative: str, expected: str) -> Path:
    path = (ROOT / relative).resolve()
    require(path.is_relative_to(ROOT) and path.is_file(), f"Missing audit artifact: {relative}")
    require(hashlib.sha256(path.read_bytes()).hexdigest() == expected, f"Audit artifact changed: {relative}")
    return path


def verify_progress(data: dict) -> dict[str, dict]:
    """Check evidence admission; semantic correspondence remains a recorded review."""
    if not PROGRESS.exists():
        return {}
    progress = read(PROGRESS)
    require(progress["schema_version"] == 1, "Unknown progress schema")
    for path, expected in progress["review_sources"].items():
        checked_file(path, expected)
    tasks = {t["id"]: t for t in data["tasks"]}
    reviews = {r["id"]: r for r in progress["reviews"]}
    require(len(reviews) == len(progress["reviews"]) and set(reviews) == set(tasks), "Progress must review every task exactly once")
    require(set(progress["task_contracts"]) == set(tasks), "Progress contract set differs")
    for ident, task in tasks.items():
        require(progress["task_contracts"][ident] == task_digest(task), f"Task changed since review: {ident}")
    certificate = progress["verification"]
    snapshot = read(checked_file(certificate["snapshot_metadata"], certificate["snapshot_metadata_sha256"]))
    builds = read(checked_file(certificate["build_report"], certificate["build_report_sha256"]))
    require(builds.get("finished_at_utc"), "Snapshot build has no terminal completion record")
    declarations = read(checked_file(certificate["declaration_report"], certificate["declaration_report_sha256"]))
    archive = checked_file(certificate["snapshot_archive"], certificate["snapshot_archive_sha256"])
    require(not snapshot["changed_while_copying"], "Unstable source snapshot")
    require(builds["snapshot"] == snapshot["snapshot_root"], "Build uses another source snapshot")
    require(builds["lean_num_threads"] == 4 and "4.35.0-rc3" in builds["lean_version"], "Audit build toolchain/thread policy mismatch")
    ax = builds["axiom_audit"]
    require(ax["exit_code"] == 0 and set(ax["allowlist"]) == {"propext", "Classical.choice", "Quot.sound"}, "Owner axiom audit did not pass")
    checked_file(ax["log"], ax["log_sha256"])
    require(declarations["exit_code"] == 0 and declarations.get("owner_unsafe_audit_passed"), "Declaration/unsafe audit did not pass")
    require(declarations.get("snapshot") == snapshot["snapshot_root"] and declarations.get("build_report_sha256") == certificate["build_report_sha256"], "Declaration check uses another frozen build")
    checked_file(declarations["log"], declarations["log_sha256"])
    checked_file(declarations["source"], declarations["source_sha256"])
    resolved = set(declarations["resolved_names"])
    audited = set(ax["modules"])
    with zipfile.ZipFile(archive) as z:
        for name, expected in snapshot["files"].items():
            require(hashlib.sha256(z.read(name)).hexdigest() == expected, f"Snapshot source changed: {name}")
    for ident, review in reviews.items():
        require(review["status"] in {"complete", "partial", "unstarted"}, f"Invalid reviewed status: {ident}")
        require(review.get("rationale"), f"Review needs a rationale: {ident}")
        task = tasks[ident]
        require(review["statement"] == task["statement"] and review["title"] == task["title"], f"Reviewed goal differs: {ident}")
        criteria = review["acceptance_coverage"]
        require(len(criteria) == len(task["acceptance"]), f"Incomplete acceptance review: {ident}")
        for index, item in enumerate(criteria, 1):
            require(item["criterion"] == f"acceptance.{index:02}" and item["text"] == task["acceptance"][index - 1], f"Acceptance text differs: {ident}")
        for evidence in review["evidence"]:
            path = evidence["file"]
            require(path in snapshot["files"] and review["source_sha256"].get(path) == snapshot["files"][path], f"Evidence source hash differs: {ident}:{path}")
        if review["status"] == "complete":
            require(review["evidence"] and not review["remaining"], f"Complete task has missing evidence/obligations: {ident}")
            goal = review.get("statement_coverage", {})
            require(goal.get("status") == "covered" and goal.get("evidence") and goal.get("correspondence"), f"Full statement not covered: {ident}")
            require(all(e.get("correspondence") for e in review["evidence"]), f"Evidence lacks goal correspondence: {ident}")
            require(all(c["status"] == "covered" and c.get("evidence") and c.get("correspondence") for c in criteria), f"Acceptance not fully covered: {ident}")
            for evidence in review["evidence"]:
                path = evidence["file"]
                module = path[:-5].replace("/", ".")
                build = builds["modules"].get(module, {})
                require(build.get("status") == "passed" and build.get("exit_code") == 0 and module in audited, f"Evidence module not built/audited: {ident}:{module}")
                require(build["source_sha256"] == snapshot["files"][path], f"Built another source: {ident}:{path}")
                require(declarations.get("module_olean_sha256", {}).get(module) == build["olean_sha256"], f"Declaration artifacts differ from rebuilt module: {ident}:{module}")
                checked_file(build["log"], build["log_sha256"])
                require(evidence["declarations"] and set(evidence["declarations"]) <= resolved, f"Unresolved declaration evidence: {ident}")
                require(all(declarations.get("declaration_owners", {}).get(n) == module for n in evidence["declarations"]), f"Declaration owner differs from evidence file: {ident}")
            supported = {(e["file"], n) for e in review["evidence"] for n in e["declarations"]}
            for criterion in [goal] + criteria:
                for evidence in criterion["evidence"]:
                    require(bool(evidence["declarations"]) and all((evidence["file"], n) in supported for n in evidence["declarations"]), f"Acceptance uses unverified evidence: {ident}")
        else:
            require(review["remaining"], f"Unfinished task needs remaining obligations: {ident}")
    return reviews


def contract(node: dict) -> dict:
    return {key: node[key] for key in (
        "id", "title", "group", "required_for_main", "dependencies", "statement",
        "proof_outline", "acceptance", "paper", "target_file",
    )} | {"remaining_obligations": node.get("remaining_obligations", []) or []}


def requirements(node: dict) -> dict[str, str]:
    result = {"statement": node["statement"]}
    for kind, field in (("acceptance", "acceptance"), ("remaining", "remaining_obligations")):
        for index, text in enumerate(node.get(field, []) or [], 1):
            result[f"{kind}.{index:02}"] = text
    return result


def make_manifest(base: dict, parts: list[dict]) -> dict:
    parents: dict[str, list[dict]] = {}
    coverage: dict[str, dict] = {}
    coverage_notes: dict[str, str] = {}
    for part in parts:
        require(not set(parents).intersection(part["parents"]), "Duplicate parent in parts")
        parents.update(part["parents"])
        require(not set(coverage).intersection(part.get("coverage", {})), "Duplicate coverage")
        coverage.update(part.get("coverage", {}))
        coverage_notes.update(part.get("coverage_notes", {}))
    require(set(parents) == {n["id"] for n in base["nodes"]}, "Parts must cover all 58 original milestones")
    milestones = []
    tasks = []
    for node in base["nodes"]:
        key = node["id"]
        steps = parents[key]
        require(bool(steps), f"Empty refinement: {key}")
        obligations = requirements(node)
        mapping = {"statement": [t["id"] for t in steps]} | coverage.get(key, {})
        milestones.append({
            "id": key, "contract": contract(node), "contract_sha256": canonical_digest(contract(node)),
            "source_status": node["status"], "completion_task": steps[-1]["id"],
            "tasks": [t["id"] for t in steps],
            "coverage": [{"id": name, "text": text, "tasks": mapping.get(name, [])}
                         for name, text in obligations.items()],
            "existing_lean_evidence": node["lean_evidence"],
            "coverage_notes": {k: v for k, v in coverage_notes.items() if k.startswith(key + ".")},
            "acceptance_tasks": sorted({ident for refs in mapping.values() for ident in refs}),
        })
        for step in steps:
            tasks.append(dict(step) | {
                "parent": key, "group": node["group"], "required_for_main": node["required_for_main"],
                "upstream_milestones": node["dependencies"], "paper": node["paper"],
                "owner_role": next((r for r, group in (
                    ("integration", {"Contracts", "Scalar", "Main"}),
                    ("radial", {"Radial"}), ("spaces", {"Analysis"}),
                    ("nonlinear", {"Nonlinear"}), ("geometry", {"Geometry"}),
                ) if node["group"] in group), "unassigned_extension"),
                "write_scope": "须按 coordination/active-workers.json 登记；此清单不分配或扩大文件写入权",
                "completion_rule": "以精确 Lean 陈述、所属模块构建及 owner-based 公理审计验收；计划字段不构成证明",
                "kind": "retained_proof" if step["status"] == "retained_proof" else "assembly" if step is steps[-1] else "proof_task",
            })
    data = {
        "schema_version": 1, "date": "2026-11-11", "source_manifest": "blueprint/manifest.json",
        "source_contracts_sha256": canonical_digest([contract(n) for n in base["nodes"]]),
        "objective": "保留完整主定理的58个里程碑，将其证明工作细分为相近粒度的可验收单元",
        "granularity": {
            "normal_new_lean_lines": [200, 600], "resplit_above": 800,
            "meaning": "行数区间是初始拆分启发式，未经实际证明校准；不是工期、完成率或可直接求和的剩余代码预测",
            "rules": ["一项明确数学输出", "至少两项具体验收条件", "明确局部依赖与上游里程碑",
                      "每个父节点的全部验收及剩余义务都有子任务承担", "超800行或出现两个独立困难时继续拆分"],
        },
        "dependency_semantics": "任务依赖 depends_on、upstream_milestones及有理由登记的extra_dependencies；每个里程碑依赖其全部子任务。保留原图所有边，细分暴露的新依赖在本层单列且检查无环，不修改权威manifest。此图不代表最优并行排程。条件性几何定理可先证明；MAIN仍须实际存在见证。",
        "status_semantics": "retained_proof保留原完整局部证明；complete表示本次逐条对应并经冻结源码构建/owner公理审计支持的局部任务；partial表示已有支持但未覆盖完整目标；planned表示尚无该任务的实际实现。任务完成不自动实例化输入结构或完成父里程碑。",
        "acceptance_semantics": "coverage中跨父remaining定位是后续实例化验收门槛，不是反向证明前提。通用定理可先证明；原里程碑的全部项目义务仍须acceptance_tasks中的下游实例化任务完成后才能声称闭合。MAIN包含全部主链任务，不能跳过这些义务。",
        "milestones": milestones, "tasks": tasks,
    }
    if PROGRESS.exists():
        progress = read(PROGRESS)
        reviews = {r["id"]: r for r in progress["reviews"]}
        for task in tasks:
            require(task["id"] in reviews, f"Task lacks a review: {task['id']}")
            review = reviews[task["id"]]
            task["review"] = review
            if task["status"] != "retained_proof":
                task["status"] = {"complete": "complete", "partial": "partial", "unstarted": "planned"}[review["status"]]
        data["progress_registry"] = "blueprint/refinement/audit/progress.json"
        data["reviewed_snapshot_utc"] = progress["captured_at_utc"]
        data["progress_scope"] = "完成数以该冻结源码的精确任务陈述为准；更晚并行修改须另行核验。"
    return data


def validate(data: dict, base: dict) -> dict:
    require(data["schema_version"] == 1, "Unknown refinement schema")
    require((ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() == base["lean_toolchain"], "Toolchain drift")
    packages = read(ROOT / "lake-manifest.json")["packages"]
    require(next(p for p in packages if p["name"] == "mathlib")["rev"] == base["mathlib_commit"], "Mathlib lock drift")
    original = {n["id"]: n for n in base["nodes"]}
    milestones = {n["id"]: n for n in data["milestones"]}
    tasks = {t["id"]: t for t in data["tasks"]}
    require(len(milestones) == len(data["milestones"]) and set(milestones) == set(original), "Milestone set changed")
    require(len(tasks) == len(data["tasks"]), "Duplicate task IDs")
    reviews = verify_progress(data)
    require(data["source_contracts_sha256"] == canonical_digest([contract(n) for n in base["nodes"]]), "Original contracts changed; regenerate refinement")
    original_graph = {n["id"]: n["dependencies"] for n in base["nodes"]}
    try:
        list(TopologicalSorter(original_graph).static_order())
    except CycleError as exc:
        raise ValueError("Original milestone graph is cyclic") from exc

    def ancestors(key: str) -> set[str]:
        found: set[str] = set()
        todo = list(original_graph[key])
        while todo:
            item = todo.pop()
            if item not in found:
                found.add(item)
                todo.extend(original_graph[item])
        return found

    graph: dict[str, list[str]] = {}
    retained = 0
    line_bands = Counter()
    for key, milestone in milestones.items():
        parent = original[key]
        for ref in parent["paper"]:
            path = (ROOT / ref["file"]).resolve()
            require(path.is_relative_to(ROOT) and path.is_file(), f"Missing/invalid manuscript path: {key}")
            source = path.read_text(encoding="utf-8")
            require(1 <= ref["start"] <= ref["end"] <= len(source.splitlines()), f"Invalid manuscript range: {key}")
            if ref.get("label"):
                require("\\label{" + ref["label"] + "}" in source, f"Missing manuscript label: {key}")
        require(milestone["contract"] == contract(parent), f"Original statement/obligations changed: {key}")
        require(milestone["contract_sha256"] == canonical_digest(contract(parent)), f"Stale contract digest: {key}")
        require(milestone["source_status"] == parent["status"], f"Stale parent status: {key}")
        require(milestone["existing_lean_evidence"] == parent["lean_evidence"], f"Stale evidence: {key}")
        owned = milestone["tasks"]
        require(bool(owned) and len(owned) == len(set(owned)), f"Invalid task list: {key}")
        require(owned == [t["id"] for t in data["tasks"] if t["parent"] == key], f"Parent membership mismatch: {key}")
        require(milestone["completion_task"] == owned[-1], f"Missing final assembly task: {key}")
        require(owned == [f"{key}.{i:02}" for i in range(1, len(owned) + 1)], f"Non-contiguous child IDs: {key}")
        expected = requirements(parent)
        rows = milestone["coverage"]
        require(milestone.get("acceptance_tasks") == sorted({ident for row in rows for ident in row["tasks"]}), f"Acceptance coverage gates differ: {key}")
        require(len(rows) == len(expected) and {r["id"] for r in rows} == set(expected), f"Requirement coverage set differs: {key}")
        for row in rows:
            require(row["text"] == expected[row["id"]], f"Requirement text changed: {key}:{row['id']}")
            refs = row["tasks"]
            require(bool(refs) and len(refs) == len(set(refs)) and set(refs) <= set(tasks), f"Missing/invalid coverage: {key}:{row['id']}")
            external = [r for r in refs if r not in owned]
            if external:
                require(row["id"].startswith("remaining."), f"Only remaining instantiation obligations may be delegated: {key}:{row['id']}")
                require(milestone.get("coverage_notes", {}).get(key + "." + row["id"]), f"External coverage needs an explanation: {key}:{row['id']}")
                require(not parent["required_for_main"] or all(tasks[r]["required_for_main"] for r in external), f"Main obligation delegated to optional work: {key}")
            if row["id"] != "statement" and len(owned) > 2:
                require(set(refs) != {owned[-1]}, f"Obligation hidden only in assembly: {key}:{row['id']}")
        graph[key] = owned
        for number, ident in enumerate(owned, 1):
            task = tasks[ident]
            require(re.fullmatch(r"(?:[A-Z]+\d+|MAIN)\.\d{2}", ident) is not None, f"Invalid task ID: {ident}")
            for field in ("title", "statement", "acceptance", "estimate_reason", "covers"):
                require(bool(task.get(field)), f"Missing {field}: {ident}")
            require(len(task["acceptance"]) >= 2, f"Insufficient acceptance: {ident}")
            require(task["upstream_milestones"] == parent["dependencies"], f"Lost original dependency: {ident}")
            require(task["paper"] == parent["paper"] and task["group"] == parent["group"], f"Source correspondence differs: {ident}")
            require(task["required_for_main"] == parent["required_for_main"], f"Main scope changed: {ident}")
            deps = task["depends_on"]
            require(len(deps) == len(set(deps)) and ident not in deps, f"Invalid dependencies: {ident}")
            for dep in deps:
                require(dep in tasks, f"Dangling task dependency: {ident} -> {dep}")
                other = tasks[dep]["parent"]
                require(other == key or other in ancestors(key), f"Unregistered cross-parent dependency: {ident} -> {dep}")
            extra = task.get("extra_dependencies", [])
            extra_ids = [d["milestone"] for d in extra]
            require(len(extra_ids) == len(set(extra_ids)), f"Duplicate extra dependency: {ident}")
            for item in extra:
                require(item["milestone"] in original and item["milestone"] != key and item.get("reason"), f"Invalid extra dependency: {ident}")
                require(item["milestone"] not in task["upstream_milestones"], f"Redundant extra dependency: {ident}")
            band = task["estimated_new_lean_lines"]
            require(len(band) == 2 and all(isinstance(x, int) for x in band) and 0 <= band[0] <= band[1] <= 800, f"Task needs resplitting: {ident}")
            if task["status"] == "retained_proof":
                require(parent["status"] == "formalized" and len(owned) == 1 and band == [0, 0], f"Unsupported completion claim: {ident}")
                retained += 1
            else:
                expected_status = {"complete": "complete", "partial": "partial", "unstarted": "planned"}.get(reviews.get(ident, {}).get("status"), "planned")
                require(task["status"] == expected_status and band[0] > 0, f"Unsupported status: {ident}")
                line_bands[tuple(band)] += 1
            if reviews:
                require(task.get("review") == reviews[ident], f"Review overlay differs: {ident}")
                if task["status"] == "retained_proof":
                    require(reviews[ident]["status"] == "complete", f"Retained result did not pass review: {ident}")
            graph[ident] = list(deps) + list(task["upstream_milestones"]) + extra_ids
    require(retained == sum(n["status"] == "formalized" for n in base["nodes"]), "Completed local results were split/lost")
    try:
        list(TopologicalSorter(graph).static_order())
    except CycleError as exc:
        raise ValueError(f"Refinement dependency cycle: {exc.args}") from exc
    for milestone in milestones.values():
        final = milestone["completion_task"]
        seen = set()
        todo = list(tasks[final]["depends_on"])
        while todo:
            item = todo.pop()
            if item not in seen:
                seen.add(item)
                todo.extend(tasks[item]["depends_on"])
        require(set(milestone["tasks"][:-1]) <= seen, f"Final assembly omits child obligations: {milestone['id']}")
    closure = set()
    todo = [base["main_node"]]
    while todo:
        item = todo.pop()
        if item not in closure:
            closure.add(item)
            todo.extend(graph[item])
    required = {n["id"] for n in base["nodes"] if n["required_for_main"]} | {t["id"] for t in tasks.values() if t["required_for_main"]}
    require(closure == required, "Refined MAIN closure differs from original required scope")
    return {
        "milestones": len(milestones), "tasks": len(tasks),
        "main_tasks": sum(t["required_for_main"] for t in tasks.values()),
        "optional_tasks": sum(not t["required_for_main"] for t in tasks.values()),
        "retained_complete_tasks": retained,
        "new_completion_claims": sum(t["status"] == "complete" for t in tasks.values()),
        "complete_tasks": sum(t["status"] in {"complete", "retained_proof"} for t in tasks.values()),
        "partial_tasks": sum(t["status"] == "partial" for t in tasks.values()),
        "planned_tasks": sum(t["status"] == "planned" for t in tasks.values()),
        "reviewed_tasks": len(reviews),
        "reviewed_snapshot_utc": data.get("reviewed_snapshot_utc"),
        "completed_ids": [t["id"] for t in tasks.values() if t["status"] in {"complete", "retained_proof"}],
        "status_by_group": {group: dict(Counter(t["status"] for t in tasks.values() if t["group"] == group)) for group in GROUPS},
        "by_group": dict(Counter(t["group"] for t in tasks.values())),
        "by_kind": dict(Counter(t["kind"] for t in tasks.values())),
        "tasks_per_milestone": {k: len(m["tasks"]) for k, m in milestones.items()},
        "line_bands": {f"{a}-{b}": count for (a, b), count in sorted(line_bands.items())},
        "dependency_edges": sum(len(v) for v in graph.values()),
        "original_requirements_covered": sum(len(m["coverage"]) for m in milestones.values()),
        "additional_dependency_edges": [{"task": t["id"], **d} for t in tasks.values() for d in t.get("extra_dependencies", [])],
        "delegated_instantiation_obligations": [{"requirement": m["id"] + "." + r["id"], "tasks": [t for t in r["tasks"] if tasks[t]["parent"] != m["id"]]} for m in milestones.values() for r in m["coverage"] if any(tasks[t]["parent"] != m["id"] for t in r["tasks"])],
        "dag_valid": True, "main_closure_preserved": True,
        "coverage_mapping_is_mathematical_proof": False, "main_formalized": False,
    }


def render(data: dict, stats: dict) -> str:
    lines = ["# 细分证明任务", "", "由 `parts/*.json` 经 `check.py --write` 生成。原58节点仍是里程碑，编号和数学要求不变。", "",
             f"共 **{stats['tasks']} 个工作单元**：主链 {stats['main_tasks']}，旁支 {stats['optional_tasks']}。完整完成 **{stats['complete_tasks']}**，部分完成 **{stats['partial_tasks']}**，尚未实现 **{stats['planned_tasks']}**。", "",
             "完成数对应冻结源码的局部任务陈述；原58个里程碑的状态不自动改变，实际Core及完整主定理仍须另行构造与验收。", "",
             "行数区间只用于控制拆分粒度；数学难度未经实际证明校准，不能据此直接计算完成百分比或剩余总行数。", "",
             "## 里程碑索引", "", "| 里程碑 | 子任务数 | 原状态 |", "| --- | ---: | --- |"]
    for m in data["milestones"]:
        lines.append(f"| [{m['id']} {m['contract']['title']}](#{m['id'].lower()}) | {len(m['tasks'])} | {m['source_status']} |")
    lookup = {t["id"]: t for t in data["tasks"]}
    for m in data["milestones"]:
        key = m["id"]
        lines += ["", f'<a id="{key.lower()}"></a>', f"## {key} {m['contract']['title']}", "",
                  "**原节点完整目标：** " + m["contract"]["statement"], "",
                  "**原上游里程碑：** " + (", ".join(m["contract"]["dependencies"]) or "无"), "",
                  "**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。", "",
                  "**论文定位：** " + "；".join(f"[{Path(r['file']).name}:{r['start']}–{r['end']}](../../{r['file']}#L{r['start']})" for r in m["contract"]["paper"]), ""]
        for ident in m["tasks"]:
            t = lookup[ident]
            a, b = t["estimated_new_lean_lines"]
            lines += [f'<a id="{ident.lower().replace(".", "-")}"></a>', f"### {ident} {t['title']}", "",
                      f"**输出：** {t['statement']}", "",
                      f"**局部依赖：** {', '.join(t['depends_on']) or '无'}。另继承上列原上游里程碑。", "",
                      f"**状态：** {t['status']}。**初始粒度：** {a}–{b} 行。{t['estimate_reason']}", "",
                      "**验收条件：**", ""] + ["- " + item for item in t["acceptance"]]
            if t.get("existing_support"):
                lines += ["", "**可复用基础：** " + str(t["existing_support"])]
            if t.get("extra_dependencies"):
                lines += ["", "**细分后补充依赖：** " + "；".join(d["milestone"] + "：" + d["reason"] for d in t["extra_dependencies"])]
            if t.get("review"):
                review = t["review"]
                lines += ["", "**本轮核对：** " + review["rationale"]]
                for evidence in review["evidence"]:
                    lines += ["", f"**源码证据 `{evidence['file']}`：** " + ", ".join(f"`{n}`" for n in evidence["declarations"]),
                              "", evidence.get("correspondence", "")]
                if review["remaining"]:
                    lines += ["", "**未完成内容：**"] + ["- " + item for item in review["remaining"]]
                lines += ["", "**逐条验收：**"]
                for criterion in review["acceptance_coverage"]:
                    lines.append(f"- {criterion['criterion']} [{criterion['status']}]：{criterion.get('correspondence', '')}")
            lines += [""]
        lines += ["**原义务覆盖表：**", "", "| 原义务 | 承担子任务 |", "| --- | --- |"]
        for row in m["coverage"]:
            refs = m["completion_task"] + "（组合全部子任务）" if row["id"] == "statement" else ", ".join(row["tasks"])
            lines.append(f"| {row['id']}：{row['text'].replace('|', ' / ')} | {refs} |")
        for ident, note in m.get("coverage_notes", {}).items():
            lines += ["", f"**覆盖说明 {ident}：** {note}"]
    return "\n".join(lines) + "\n"


def overview(data: dict, stats: dict) -> str:
    lines = ["# 细分任务总览", "", f"原58个里程碑展开为 **{stats['tasks']} 个工作单元**，其中主链 {stats['main_tasks']} 个、加强旁支 {stats['optional_tasks']} 个。", "",
             f"本轮完整完成 **{stats['complete_tasks']}**，部分完成 **{stats['partial_tasks']}**，尚未实现 **{stats['planned_tasks']}**；核对 {stats['reviewed_tasks']} 项。详见 [逐项验收与构建证据](AUDIT.md)。", "",
             "| 工作包 | 单元数 | 完整完成 | 部分完成 | 尚未实现 |", "| --- | ---: | ---: | ---: | ---: |"]
    for group, title in GROUPS.items():
        statuses = stats["status_by_group"][group]
        lines.append(f"| {title} | {stats['by_group'].get(group, 0)} | {statuses.get('complete', 0) + statuses.get('retained_proof', 0)} | {statuses.get('partial', 0)} | {statuses.get('planned', 0)} |")
    lines += ["", "## 每个工作单元", "", "| 任务 | 当前状态 | 直接子任务依赖 | 初始行数粒度 |", "| --- | --- | --- | ---: |"]
    for task in data["tasks"]:
        ident = task["id"]
        lo, hi = task["estimated_new_lean_lines"]
        state = {"retained_proof": "完整完成（原有）", "complete": "完整完成", "partial": "部分完成", "planned": "尚未实现"}[task["status"]]
        lines.append(f"| [{ident} {task['title']}](NODES.md#{ident.lower().replace('.', '-')}) | {state} | {', '.join(task['depends_on']) or '无'} | {lo}–{hi} |")
    lines += ["", "上游里程碑依赖、明确补充依赖、精确数学目标、论文位置和验收条件见详细任务页。行数为规划启发式，不能直接换算完成率或总工期。"]
    return "\n".join(lines) + "\n"


def audit_summary(data: dict, stats: dict) -> str:
    captured = data.get("reviewed_snapshot_utc")
    local_time = datetime.fromisoformat(captured).astimezone(timezone(timedelta(hours=8), "Asia/Taipei")).strftime("%Y-%m-%d %H:%M:%S") if captured else "未核验"
    lines = ["# 现有成果逐项验收", "", f"已核对 **{stats['reviewed_tasks']} / {stats['tasks']}** 个单位。完整完成 **{stats['complete_tasks']}**，部分完成 **{stats['partial_tasks']}**，尚未实现 **{stats['planned_tasks']}**。", "",
             f"冻结源码时间（台北）：`{local_time}`。完成数只对应这份源码及原任务的完整数学目标/全部验收条件，更晚并行成果须后续核验。", "",
             "**完成含义：** 局部或通用条件定理的全部任务输出已有真实Lean证据；并不证明输入结构非空，不自动完成父里程碑或完整MAIN。原58节点状态保持原样。", ""]
    if PROGRESS.exists():
        progress = read(PROGRESS)
        verification = progress["verification"]
        build = read(ROOT / verification["build_report"])
        passed = sum(r["status"] == "passed" for r in build["modules"].values())
        failed = [name for name, r in build["modules"].items() if r["status"] != "passed"]
        lines += [f"隔离构建：{passed} / {len(build['modules'])} 个快照模块通过。所有计入完成的证据模块均构建通过，且在owner-based公理审计范围；允许公理仅propext、Classical.choice、Quot.sound，并另检查项目unsafe声明。", "",
                  "未通过/受阻模块：" + (", ".join(f"`{n}`" for n in failed) or "无") + "。这些模块不作为完整完成的证明证据。", "",
                  "- [逐项机器记录](audit/progress.json)", "- [冻结源码元数据](audit/source-snapshot.json)", "- [冻结源码归档](audit/source-snapshot.zip)",
                  "- [实际模块构建终态](audit/build-results.json)", "- [声明解析及unsafe审计](audit/declaration-check.json)", ""]
    lines += ["## 全部单位核对结果", "", "| 单位 | 结论 | 依据或缺口 |", "| --- | --- | --- |"]
    for task in data["tasks"]:
        ident = task["id"]
        review = task.get("review", {})
        state = {"retained_proof": "完整完成（原有）", "complete": "完整完成", "partial": "部分完成", "planned": "尚未实现"}[task["status"]]
        explanation = review.get("rationale", "尚未核验").replace("|", " / ").replace("\n", " ")
        lines.append(f"| [{ident} {task['title']}](NODES.md#{ident.lower().replace('.', '-')}) | {state} | {explanation} |")
    return "\n".join(lines) + "\n"


def mermaid(data: dict) -> str:
    lines = ["flowchart LR"]
    for m in data["milestones"]:
        key = m["id"]
        lines.append(f'  {key}["{key} {m["contract"]["title"]}"]')
    for t in data["tasks"]:
        ident = t["id"].replace(".", "_")
        lines.append(f'  {ident}["{t["id"]} {t["title"].replace(chr(34), chr(39))}"]')
        for dep in t["depends_on"] + t["upstream_milestones"] + [d["milestone"] for d in t.get("extra_dependencies", [])]:
            lines.append(f"  {dep.replace('.', '_')} --> {ident}")
        lines.append(f"  {ident} --> {t['parent']}")
    lines += ["  classDef complete fill:#dcfce7,stroke:#166534", "  classDef partial fill:#fef3c7,stroke:#92400e"]
    for task in data["tasks"]:
        kind = "complete" if task["status"] in {"complete", "retained_proof"} else "partial" if task["status"] == "partial" else None
        if kind:
            lines.append(f"  class {task['id'].replace('.', '_')} {kind}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Regenerate refinement artifacts only")
    args = parser.parse_args()
    base = read(BASE)
    parts = [read(p) for p in sorted(PARTS.glob("*.json"))]
    data = make_manifest(base, parts)
    stats = validate(data, base)
    outputs = {
        "manifest.json": json.dumps(data, ensure_ascii=False, indent=2) + "\n",
        "NODES.md": render(data, stats), "DEPENDENCIES.mmd": mermaid(data),
        "OVERVIEW.md": overview(data, stats),
        "AUDIT.md": audit_summary(data, stats),
        "validation.json": json.dumps(stats, ensure_ascii=False, indent=2) + "\n",
    }
    for name, content in outputs.items():
        path = HERE / name
        if args.write:
            path.write_text(content, encoding="utf-8")
        else:
            require(path.exists() and path.read_text(encoding="utf-8") == content, f"Stale refinement artifact: {name}; run check.py --write")
    print(json.dumps(stats, ensure_ascii=False))


if __name__ == "__main__":
    main()
