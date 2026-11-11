"""Validate and render the repository's mathematical proof blueprint.

This checks dependency and source correspondence. It does not verify the
mathematical claims of planned nodes; Lean remains the proof verifier.
Only Python's standard library is required.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from graphlib import CycleError, TopologicalSorter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BLUEPRINT = ROOT / "blueprint"
MANIFEST = BLUEPRINT / "manifest.json"
BASELINE = BLUEPRINT / "proof-baseline.json"
PUBLIC_THEOREM = r"^(?:@\[[^\]\n]*\]\s*)*(?:theorem|lemma)\s+"
STATUS = {"formalized": "已形式化的局部节点", "partial": "已有部分已编译子结果", "specified": "已写规格，未编译", "planned": "待形式化"}
GROUPS = {
    "Contracts": "目标与接口", "Scalar": "标量方程", "Radial": "径向参考",
    "Analysis": "分析基础与加权空间", "Nonlinear": "非线性存在性",
    "Geometry": "几何闭合", "Main": "主定理", "Extensions": "主定理之后的加强",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def workspace_file(relative: str) -> Path:
    path = (ROOT / relative).resolve()
    require(path.is_relative_to(ROOT), f"Path leaves workspace: {relative}")
    return path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_proof_snapshot() -> dict[str, str]:
    paths = list((ROOT / "ContinuousFlexibility").rglob("*.lean"))
    paths += [ROOT / name for name in (
        "ContinuousFlexibility.lean", "AxiomAudit.lean", "lean-toolchain",
        "lakefile.toml", "lake-manifest.json",
    )]
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(paths)}


def public_theorem_locations(path: Path) -> dict[tuple[str, str], int]:
    """Read explicit source declarations with their actual namespace context.

    Namespace and section commands in the project occupy separate lines.
    Tracking sections prevents a section's `end` from closing a namespace.
    Lean's compiled environment remains the authority for proof checking.
    """
    frames: list[tuple[str, str]] = []
    result: dict[tuple[str, str], int] = {}
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        namespace = re.match(r"^namespace\s+(\S+)\s*$", line)
        section = re.match(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$", line)
        ending = re.match(r"^end(?:\s+(\S+))?\s*$", line)
        if namespace:
            frames.append(("namespace", namespace[1]))
        elif section:
            frames.append(("section", section[1] or ""))
        elif ending:
            require(bool(frames), f"Unmatched source end: {path}:{number}")
            kind, name = frames.pop()
            if ending[1]:
                require(name == ending[1], f"Unexpected source end: {path}:{number}")
        declaration = re.match(PUBLIC_THEOREM + r"(\S+)", line)
        if declaration:
            context = ".".join(name for kind, name in frames if kind == "namespace")
            key = (context, declaration[1])
            require(key not in result, f"Duplicate public declaration: {path}: {key}")
            result[key] = number
    return result


def evidence_sources(data: dict, full_workspace: bool = False) -> tuple[list[Path], dict]:
    """Keep audited source hashes distinct from explicitly owned parallel drafts.

    The checkpoint records an actual build/audit performed by integration.
    This function checks its present source identity, not its mathematical proof.
    Full-workspace mode keeps the original strict coverage rule for final gates.
    """
    current = sorted((ROOT / "ContinuousFlexibility").rglob("*.lean"))
    checkpoint_name = None if full_workspace else data.get("proof_checkpoint")
    excluded: list[str] = []
    if checkpoint_name:
        checkpoint = json.loads(workspace_file(checkpoint_name).read_text(encoding="utf-8"))
        build = checkpoint["build"]
        require(build["terminal_exit_code"] == 0 and build["warnings"] == 0,
                "Proof checkpoint lacks a successful zero-warning build")
        require(build["audit_declarations"] > 0 and build["audit_theorems"] > 0,
                "Proof checkpoint has no nonvacuous owner audit")
        require(set(checkpoint["axiom_allowlist"]) == {"propext", "Classical.choice", "Quot.sound"},
                "Proof checkpoint has an unexpected axiom allowance")
        require(checkpoint["toolchain"] == data["lean_toolchain"], "Checkpoint/toolchain mismatch")
        require(checkpoint["mathlib_commit"] == data["mathlib_commit"], "Checkpoint/mathlib mismatch")
        sources = checkpoint["sources"]
        require("ContinuousFlexibility.lean" in sources and "AxiomAudit.lean" in sources,
                "Proof checkpoint must bind the root entry point and owner audit")
        for name, metadata in sources.items():
            require(name.endswith(".lean"), f"Non-Lean checkpoint source: {name}")
            path = workspace_file(name)
            require(path.is_file() and digest(path) == metadata["sha256"],
                    f"Audited source changed since checkpoint: {name}")
        root_imports = workspace_file("ContinuousFlexibility.lean").read_text(encoding="utf-8")
        for module in re.findall(r"^import\s+(ContinuousFlexibility\.[\w.]+)\s*$", root_imports, re.M):
            require(module.replace(".", "/") + ".lean" in sources,
                    f"Checkpoint omits an imported project module: {module}")
        included = [p for p in current if p.relative_to(ROOT).as_posix() in sources]
        excluded = [p.relative_to(ROOT).as_posix() for p in current if p not in included]
        # Nothing may silently disappear from the project while it is being developed.
        registry = json.loads(workspace_file("coordination/active-workers.json").read_text(encoding="utf-8"))
        for name in excluded:
            owners = {w["worker"] for w in registry["workers"]
                      for scope in w["scope"] + w.get("frozen_deliveries", [])
                      if name == scope.rstrip("/") or name.startswith(scope.rstrip("/") + "/")}
            require(len(owners) == 1, f"Source outside checkpoint lacks a unique registered owner: {name}")
    else:
        included = current
    root_imports = workspace_file("ContinuousFlexibility.lean").read_text(encoding="utf-8")
    for path in included:
        module = path.relative_to(ROOT).as_posix()[:-5].replace("/", ".")
        require(re.search(r"^import\s+" + re.escape(module) + r"\s*$", root_imports, re.M),
                f"Project module absent from audit entry point: {module}")
    return included, {"proof_checkpoint": checkpoint_name,
                      "checked_project_modules": len(included),
                      "excluded_unverified_sources": excluded}


def validate(data: dict, full_workspace: bool = False) -> tuple[list[dict], dict]:
    require(data["schema_version"] == 1, "Unknown blueprint schema")
    nodes = data["nodes"]
    by_id = {node["id"]: node for node in nodes}
    require(len(nodes) == len(by_id), "Duplicate node IDs")
    for node in nodes:
        key = node["id"]
        require(re.fullmatch(r"(?:[A-Z]+\d+|MAIN)", key) is not None, f"Invalid ID: {key}")
        require(node["status"] in STATUS, f"Invalid status: {key}")
        require(node["group"] in GROUPS, f"Invalid group: {key}")
        for field in ("title", "statement", "proof_outline", "acceptance", "paper", "target_file"):
            require(bool(node.get(field)), f"Missing {field}: {key}")
        deps = node["dependencies"]
        require(len(deps) == len(set(deps)), f"Duplicate dependencies: {key}")
        for dep in deps:
            require(dep in by_id and dep != key, f"Invalid dependency {dep} of {key}")
        if node["status"] in {"formalized", "partial"}:
            require(bool(node["lean_evidence"]), f"Formalized node lacks evidence: {key}")
            if node["status"] == "formalized":
                require(all(by_id[d]["status"] == "formalized" for d in deps),
                        f"Formalized node depends on an unproved node: {key}")
            else:
                require(node.get("implementation_progress") and
                        (node.get("current_remaining_obligations") or node.get("remaining_obligations")),
                        f"Partial node must state both progress and remaining obligations: {key}")
        else:
            require(not node["lean_evidence"], f"Unproved node carries completed evidence: {key}")
        for ref in node["paper"]:
            path = workspace_file(ref["file"])
            require(path.is_file(), f"Missing manuscript file: {ref['file']}")
            content = path.read_text(encoding="utf-8")
            require(1 <= ref["start"] <= ref["end"] <= len(content.splitlines()),
                    f"Invalid manuscript line range: {key}: {ref}")
            if "label" in ref:
                require("\\label{" + ref["label"] + "}" in content,
                        f"Missing manuscript label: {key}: {ref['label']}")
    try:
        order = list(TopologicalSorter({n["id"]: n["dependencies"] for n in nodes}).static_order())
    except CycleError as exc:
        raise ValueError(f"Circular proof dependency: {exc.args}") from exc

    main = data["main_node"]
    require(main in by_id, "Main theorem node is missing")
    ancestors: set[str] = set()

    def visit(key: str) -> None:
        if key in ancestors:
            return
        ancestors.add(key)
        for dep in by_id[key]["dependencies"]:
            visit(dep)

    visit(main)
    required = {n["id"] for n in nodes if n["required_for_main"]}
    require(ancestors == required,
            f"Main ancestry mismatch: missing={sorted(required-ancestors)}, optional={sorted(ancestors-required)}")

    included, scope = evidence_sources(data, full_workspace)
    included_names = {p.relative_to(ROOT).as_posix() for p in included}
    require(not (by_id[main]["status"] == "formalized" and scope["excluded_unverified_sources"]),
            "MAIN completion requires coverage of the entire current project")
    covered: set[tuple[str, str, str]] = set()
    for node in nodes:
        for evidence in node["lean_evidence"]:
            require(evidence["file"] in included_names,
                    f"Lean evidence is outside the checked proof scope: {evidence['file']}")
            path = workspace_file(evidence["file"])
            locations = public_theorem_locations(path)
            for declaration in evidence["declarations"]:
                pair = (evidence["file"], evidence["namespace"], declaration)
                require(pair not in covered, f"Theorem assigned to multiple nodes: {pair}")
                require((evidence["namespace"], declaration) in locations,
                        f"Missing actual Lean theorem: {pair}")
                covered.add(pair)

    actual = set()
    for path in included:
        relative = path.relative_to(ROOT).as_posix()
        for namespace, declaration in public_theorem_locations(path):
            actual.add((relative, namespace, declaration))
    require(covered == actual,
            f"Lean coverage mismatch: unassigned={sorted(actual-covered)}, stale={sorted(covered-actual)}")

    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    require(toolchain == data["lean_toolchain"], "Blueprint/toolchain mismatch")
    locked = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(p for p in locked["packages"] if p["name"] == "mathlib")
    require(mathlib["rev"] == data["mathlib_commit"], "Blueprint/mathlib lock mismatch")
    archive = ROOT / "flex-rewrite-62pp-tex.zip"
    require(digest(archive).upper() == data["paper_sha256"], "Manuscript archive hash changed")

    coordination = ROOT / "coordination" / "assignments.json"
    role_count = 0
    if coordination.exists():
        registry = json.loads(coordination.read_text(encoding="utf-8"))
        require(registry["toolchain"] == toolchain, "Coordination/toolchain mismatch")
        require(registry["mathlib_commit"] == mathlib["rev"], "Coordination/mathlib mismatch")
        roles = registry["roles"]
        owners = [key for role in roles for key in role["nodes"]]
        require(len(owners) == len(set(owners)), "Multiple coordination roles own a node")
        require(set(owners) == required, "Coordination roles must cover the full main dependency closure")
        role_count = len(roles)

    stats = {
        "nodes": len(nodes), "required_for_main": len(required),
        "formalized_local_nodes": sum(n["status"] == "formalized" for n in nodes),
        "partially_implemented_nodes": sum(n["status"] == "partial" for n in nodes),
        "specified_nodes": sum(n["status"] == "specified" for n in nodes),
        "planned_nodes": sum(n["status"] == "planned" for n in nodes),
        "optional_nodes": len(nodes) - len(required), "mapped_explicit_lean_theorems": len(covered),
        "dependency_edges": sum(len(n["dependencies"]) for n in nodes),
        "main_formalized": by_id[main]["status"] == "formalized",
        "coordination_roles": role_count,
        **scope,
    }
    return [by_id[key] for key in order], stats


def source_link(ref: dict) -> str:
    label = f"{Path(ref['file']).name}:{ref['start']}–{ref['end']}"
    suffix = f"，`{ref['label']}`" if ref.get("label") else ""
    return f"[{label}](../{ref['file']}#L{ref['start']}){suffix}"


def render_nodes(data: dict, ordered: list[dict], stats: dict) -> str:
    lines = [
        "# 主定理形式化节点清单", "",
        "由 `manifest.json` 生成。修改清单后运行 `python scripts/check_blueprint.py --write`。", "",
        "状态只对本节点的精确陈述有效。计划中的陈述和证明提纲尚未通过 Lean；依赖图通过检查不等于数学证明成立。", "",
        f"共 {stats['nodes']} 个节点，主链 {stats['required_for_main']} 个，旁支 {stats['optional_nodes']} 个；"
        f"{stats['formalized_local_nodes']} 个已完成局部节点，{stats['partially_implemented_nodes']} 个部分实现节点，"
        f"共同记录现有 {stats['mapped_explicit_lean_theorems']} 条公开显式定理。", "",
    ]
    if stats["proof_checkpoint"]:
        lines += ["", f"证明源码范围固定于 `{stats['proof_checkpoint']}`，逐文件核对当前哈希；"
                  f"另有 {len(stats['excluded_unverified_sources'])} 个已登记负责人的源码文件未计入本检查点（含并行草稿及后续交付）。", ""]
    lines += ["## 拓扑顺序索引", "", "| 节点 | 状态 | 直接依赖 |", "| --- | --- | --- |"]
    for node in ordered:
        deps = ", ".join(node["dependencies"]) or "—"
        status = STATUS[node["status"]] + ("；加强旁支" if not node["required_for_main"] else "")
        lines.append(f"| [{node['id']} {node['title']}](#{node['id'].lower()}) | {status} | {deps} |")
    for node in data["nodes"]:
        lines += ["", f"<a id=\"{node['id'].lower()}\"></a>", f"## {node['id']} {node['title']}", "",
                  f"**状态：** {STATUS[node['status']]}。**分支：** {GROUPS[node['group']]}。"
                  + ("主定理必要节点。" if node["required_for_main"] else "主定理之后的加强旁支。"), "",
                  "**数学陈述：** " + node["statement"], "",
                  "**证明提纲：** " + node["proof_outline"], "",
                  "**直接依赖：** " + (", ".join(f"[{d}](#{d.lower()})" for d in node["dependencies"]) or "无其他蓝图节点"), "",
                  "**论文定位：** " + "；".join(source_link(ref) for ref in node["paper"]), "",
                  f"**目标文件：** `{node['target_file']}`" + ("（已有）" if node["status"] == "formalized" else "（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）" if node["status"] == "partial" else "（拟建，尚无此证明）"), "",
                  "**验收条件：**", ""]
        lines += ["- " + gate for gate in node["acceptance"]]
        if node.get("implementation_progress"):
            lines += ["", "**已经完成的子结果：**", ""]
            lines += ["- " + item for item in node["implementation_progress"]]
        remaining = node.get("current_remaining_obligations", node.get("remaining_obligations"))
        if remaining:
            lines += ["", "**仍待闭合的义务：**", ""]
            lines += ["- " + item for item in remaining]
        if node.get("external_reference"):
            lines += ["", "**外部原始定理：** " + node["external_reference"]]
        if node.get("route_decision"):
            lines += ["", "**路线决策：** " + node["route_decision"]]
        if node.get("risk"):
            lines += ["", "**优先核查程度：** " + node["risk"] + "（任务风险标记，不是已发现错误）"]
        if node["lean_evidence"]:
            lines += ["", "**现有 Lean 证明：**", ""]
            for item in node["lean_evidence"]:
                locations = public_theorem_locations(workspace_file(item["file"]))
                lines.append(f"[{Path(item['file']).name}](../{item['file']})：")
                lines.append("")
                for declaration in item["declarations"]:
                    number = locations[(item["namespace"], declaration)]
                    full = item["namespace"] + "." + declaration
                    lines.append(f"- [`{full}`](../{item['file']}#L{number})")
                lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def render_mermaid(data: dict) -> str:
    lines = ["flowchart LR"]
    for group, title in GROUPS.items():
        grouped = [n for n in data["nodes"] if n["group"] == group]
        if not grouped:
            continue
        lines += [f'  subgraph {group}["{title}"]']
        for node in grouped:
            title = node["title"].replace('"', "&quot;")
            lines.append(f'    {node["id"]}["{node["id"]} {title}"]')
        lines.append("  end")
    for node in data["nodes"]:
        arrow = "-->" if node["required_for_main"] else "-.->"
        for dep in node["dependencies"]:
            lines.append(f'  {dep} {arrow} {node["id"]}')
    lines += [
        "  classDef formalized fill:#dcfce7,stroke:#15803d,color:#14532d",
        "  classDef partial fill:#ffedd5,stroke:#ea580c,color:#7c2d12",
        "  classDef specified fill:#dbeafe,stroke:#2563eb,color:#1e3a8a",
        "  classDef planned fill:#f8fafc,stroke:#64748b,color:#0f172a",
        "  classDef extension fill:#fef3c7,stroke:#b45309,color:#78350f",
    ]
    for node in data["nodes"]:
        style = node["status"] if node["required_for_main"] else "extension"
        lines.append(f'  class {node["id"]} {style}')
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write generated blueprint files")
    parser.add_argument("--record-baseline", action="store_true", help="Record the current proof/config hashes")
    parser.add_argument("--check-proof-baseline", action="store_true", help="Also require the blueprint-only milestone's unchanged proof/config snapshot")
    parser.add_argument("--all-current-sources", action="store_true",
                        help="Require every live project module, including parallel drafts; mandatory for final completion")
    args = parser.parse_args()
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    ordered, stats = validate(data, full_workspace=args.all_current_sources)
    snapshot = current_proof_snapshot()
    if args.record_baseline:
        require(not BASELINE.exists(), "Refusing to replace an existing proof baseline")
        BASELINE.write_text(json.dumps({"date": data["date"], "files": snapshot}, indent=2) + "\n", encoding="utf-8")
    require(BASELINE.exists(), "Proof baseline is missing; record it explicitly")
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))["files"]
    unchanged = snapshot == baseline
    if args.check_proof_baseline or args.record_baseline:
        require(unchanged, "Lean proof or pinned configuration changed during this blueprint-only milestone")
    outputs = {
        BLUEPRINT / "NODES.md": render_nodes(data, ordered, stats),
        BLUEPRINT / "DEPENDENCIES.mmd": render_mermaid(data),
        BLUEPRINT / "validation.json": json.dumps({
            "date": data["date"], "validation_scope": "DAG, source references, exact theorem coverage within the declared proof scope and dependency pins; checkpoint hashes are checked and parallel drafts are explicitly excluded; not mathematical proof verification",
            "checks": {"acyclic": True, "no_dangling_dependencies": True,
                       "main_ancestry_matches_required_nodes": True, "paper_references_exist": True,
                       "all_checked_public_explicit_theorems_mapped_once": True,
                       "all_current_project_sources_in_proof_scope": not stats["excluded_unverified_sources"]},
            "historical_proof_baseline": {
                "matches_current": unchanged,
                "purpose": "Immutable snapshot of the earlier blueprint-only milestone; later proof implementation is expected to change it. Use --check-proof-baseline only to enforce that historical restriction.",
            },
            **stats,
        }, ensure_ascii=False, indent=2) + "\n",
    }
    for path, content in outputs.items():
        if args.write:
            path.write_text(content, encoding="utf-8")
        else:
            require(path.exists() and path.read_text(encoding="utf-8") == content,
                    f"Generated blueprint is stale: {path.relative_to(ROOT)}")
    print(json.dumps({"blueprint_validation": "passed", **stats}, ensure_ascii=False))


if __name__ == "__main__":
    main()
