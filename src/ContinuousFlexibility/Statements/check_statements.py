"""Build and bind the 58 explicit target types to their blueprint sources.

This checks statement declarations, not proofs of those propositions.  The
authoritative proof-progress manifest remains blueprint/manifest.json.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BLUEPRINT = ROOT / "blueprint/manifest.json"
PREFIX = "ContinuousFlexibility.Statements."
TARGETS = [PREFIX + "Milestones", PREFIX + "Audit"]
EXTRA_TARGET = PREFIX + "MainGeometryAudit"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def source_inventory():
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(HERE.glob("*.lean"))}


def project_closure(roots):
    """Resolve actual project imports; external packages are locked separately."""
    found = {}
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in found:
            continue
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise ValueError(f"Missing imported project source: {module}")
        found[module] = path
        code = strip_comments_and_strings(path.read_text(encoding="utf-8-sig"))
        for imports in re.findall(r"(?m)^\s*(?:(?:public|private)\s+)?import\s+([^\r\n]+)", code):
            pending.extend(m for m in imports.split() if m == "ContinuousFlexibility" or m.startswith("ContinuousFlexibility."))
    return found


def declarations(nodes):
    found = {}
    for path in sorted(HERE.glob("*.lean")):
        content = path.read_text(encoding="utf-8-sig")
        for match in re.finditer(r"(?m)^(?:def|abbrev) ([A-Z][A-Z0-9]*Statement)\s*:\s*Prop\s*:=", content):
            name = match.group(1)
            if name in found:
                raise ValueError(f"Duplicate target declaration: {name}")
            found[name] = {
                "file": path.relative_to(ROOT).as_posix(),
                "line": content[: match.start()].count("\n") + 1,
                "declaration": PREFIX + name,
                "module": PREFIX + path.stem,
            }
    expected = {n["id"] + "Statement" for n in nodes}
    missing = expected - found.keys()
    if missing:
        raise ValueError(f"Missing target declarations: {sorted(missing)}")
    return found


def verify_registry(nodes):
    content = (HERE / "Milestones.lean").read_text(encoding="utf-8")
    actual = re.findall(r"(?m)^  \| \.([A-Z][A-Z0-9]*) => ([A-Z][A-Z0-9]*Statement)$", content)
    expected = [(n["id"], n["id"] + "Statement") for n in nodes]
    if actual != expected or len(actual) != 58:
        raise ValueError("The Lean registry does not match all 58 blueprint nodes exactly")


def strip_comments_and_strings(text):
    # Lean block comments nest. Strings are ignored when enforcing code policy.
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            out.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def verify_policy(paths=None):
    prohibited = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|partial)\b")
    for path in HERE.glob("*.lean") if paths is None else paths:
        code = strip_comments_and_strings(path.read_text(encoding="utf-8-sig"))
        # Dotted API names such as info.isUnsafe are not unsafe declarations.
        match = prohibited.search(code)
        if match:
            raise ValueError(f"Prohibited source token {match.group()} in {path.name}")


def make_manifest(nodes, decls, inventory, build):
    entries = []
    paper_hashes = {}
    for node in nodes:
        for ref in node["paper"]:
            paper_hashes[ref["file"]] = sha(ROOT / ref["file"])
        entries.append({
            "id": node["id"],
            "title": node["title"],
            "required_for_main": node["required_for_main"],
            **decls[node["id"] + "Statement"],
            "type": "Prop",
            "role": "specification_alias_of_MAIN" if node["id"] == "C00" else "theorem_goal",
            "quantifier_scope": "joint_stage_construction_exists" if node["id"].startswith("N") or node["id"] == "X02" else "explicit_in_lean_declaration",
            "statement_status": "compiled",
            "proof_status": "no_proof_of_this_target_asserted",
            "paper": node["paper"],
            "blueprint_statement": node["statement"],
            "blueprint_acceptance": node["acceptance"],
            "blueprint_dependencies": node["dependencies"],
            "alignment": "human_reviewed_not_a_machine_checked_equivalence",
        })
        if node["id"] == "W02":
            entries[-1]["source_measure_correspondence"] = {
                "W02": PREFIX + "IsPhysicalSpaces",
                "R02": PREFIX + "LiouvilleFullTransport",
                "N04": PREFIX + "N04Properties",
                "N07": PREFIX + "ScalarBanachBridgeProperties",
                "note": "W02 constructs generic spaces; actual spectral and canonical source transport is instantiated at R02 and N04/N07, avoiding a cyclic dependency on canonical charts.",
            }
    return {
        "schema_version": 1,
        "scope": "explicit_milestone_types_only",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "milestone_count": len(entries),
        "main_dependency_count": sum(n["required_for_main"] for n in nodes),
        "optional_count": sum(not n["required_for_main"] for n in nodes),
        "C00_semantics": "Specification artifact only: its target aliases MAIN, without proving existence or creating an independent MAIN premise.",
        "warning": "Compiled proposition types are not proofs or existence witnesses. This does not update proof completion counts.",
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lake_manifest_sha256": sha(ROOT / "lake-manifest.json"),
        "blueprint_sha256": sha(BLUEPRINT),
        "paper_sha256": paper_hashes,
        "lean_source_sha256": inventory,
        "new_imports": {p.name: re.findall(r"(?m)^import (\S+)", p.read_text(encoding="utf-8")) for p in sorted(HERE.glob("*.lean"))},
        "build": build,
        "nodes": entries,
    }


def check_saved(inventory):
    manifest = read_json(HERE / "manifest.json")
    if manifest["lean_source_sha256"] != inventory:
        raise ValueError("Statement sources changed since the recorded build")
    if manifest["milestone_count"] != 58:
        raise ValueError("Saved registry does not contain 58 targets")
    if sha(BLUEPRINT) != manifest["blueprint_sha256"]:
        raise ValueError("Blueprint statements or acceptance conditions changed since the recorded build")
    if sha(ROOT / "lake-manifest.json") != manifest["lake_manifest_sha256"]:
        raise ValueError("Dependency lock changed since the recorded build")
    for rel, digest in manifest["paper_sha256"].items():
        if sha(ROOT / rel) != digest:
            raise ValueError(f"Manuscript source changed: {rel}")
    for rel, digest in manifest["project_source_sha256"].items():
        if sha(ROOT / rel) != digest:
            raise ValueError(f"Audited project source changed: {rel}")
    for rel, digest in manifest["build"]["olean_sha256"].items():
        if sha(ROOT / rel) != digest:
            raise ValueError(f"Compiled artifact changed: {rel}")
    if sha(HERE / "build.log") != manifest["build"]["log_sha256"]:
        raise ValueError("Build log changed")
    print("58/58 explicit closed proposition types verified against recorded build artifacts; proof progress unchanged.")


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="build targets and audit, then refresh statement-only manifest")
    args = parser.parse_args()
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.35.0-rc3":
        raise ValueError("Unexpected Lean toolchain")
    mathlib = [p for p in read_json(ROOT / "lake-manifest.json")["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != "c55e6e786f49471c72fbddbec5415808896aec1e":
        raise ValueError("Unexpected locked mathlib revision")
    nodes = read_json(BLUEPRINT)["nodes"]
    if len(nodes) != 58 or len({n["id"] for n in nodes}) != 58:
        raise ValueError("Expected exactly 58 distinct blueprint milestones")
    decls = declarations(nodes)
    verify_registry(nodes)
    verify_policy()
    inventory = source_inventory()
    if not args.build:
        check_saved(inventory)
        return
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "4"
    closure = project_closure([*TARGETS, EXTRA_TARGET])
    verify_policy(closure.values())
    project_inventory = {p.relative_to(ROOT).as_posix(): sha(p) for p in closure.values()}
    context_paths = {BLUEPRINT, ROOT / "lean-toolchain", ROOT / "lake-manifest.json"}
    context_paths.update(ROOT / ref["file"] for node in nodes for ref in node["paper"])
    context_inventory = {p: sha(p) for p in context_paths}
    audit_imports = set(project_closure([PREFIX + "Audit"]))
    commands = [["lake", "--wfail", "build", EXTRA_TARGET],
                ["lake", "--wfail", "build", *TARGETS]]
    started = datetime.now(timezone.utc)
    output = ""
    stages = []
    for command in commands:
        result = subprocess.run(command, cwd=ROOT, env=env, text=True, encoding="utf-8", errors="replace", stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output += result.stdout
        stages.append({"command": command, "exit_code": result.returncode})
        (HERE / "build.log").write_text(output, encoding="utf-8")
        print(result.stdout, end="")
        if result.returncode:
            raise RuntimeError(f"Target build or audit failed with exit code {result.returncode}")
    if inventory != source_inventory():
        raise ValueError("A statement source changed during its build; rerun after it is stable")
    for rel, digest in project_inventory.items():
        if sha(ROOT / rel) != digest:
            raise ValueError(f"An imported project source changed during the build: {rel}")
    for path, digest in context_inventory.items():
        if sha(path) != digest:
            raise ValueError(f"Blueprint, manuscript, or dependency context changed during the build: {path}")
    audit = re.search(r"STATEMENT_AUDIT\|milestones=58\|target_declarations=(\d+)\|target_generated_theorems=(\d+)\|project_declarations=(\d+)\|axioms=\[([^\]]*)\]", output)
    if not audit:
        raise ValueError("No successful 58-target owner-based axiom audit was observed")
    observed_axioms = sorted(a.strip() for a in audit[4].split(",") if a.strip())
    if observed_axioms != ["Classical.choice", "Quot.sound", "propext"]:
        raise ValueError(f"Unexpected audited axioms: {observed_axioms}")
    compiler_recursions = re.search(r"STATEMENT_COMPILER_RECURSION\|(\d+)", output)
    if not compiler_recursions:
        raise ValueError("No compiler recursion classification was observed")
    imported = re.search(r"STATEMENT_IMPORTS\|([^\r\n]*)", output)
    if not imported or set(imported[1].strip().split(",")) != audit_imports:
        raise ValueError("Actual audited module owners do not match the resolved project import closure")
    olean = {}
    for module in sorted(closure):
        path = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        if not path.is_file():
            raise ValueError(f"Missing required compiled artifact: {module}")
        olean[path.relative_to(ROOT).as_posix()] = sha(path)
    build = {
        "commands": commands,
        "stages": stages,
        "LEAN_NUM_THREADS": 4,
        "exit_code": result.returncode,
        "started_at_utc": started.isoformat(),
        "finished_at_utc": datetime.now(timezone.utc).isoformat(),
        "audit": {"milestones": 58, "target_declarations": int(audit[1]), "target_generated_theorems": int(audit[2]), "project_declarations": int(audit[3]), "observed_axioms": observed_axioms, "compiler_generated_recursion_auxiliaries": int(compiler_recursions[1])},
        "log_sha256": sha(HERE / "build.log"),
        "olean_sha256": olean,
        "audited_project_modules": sorted(audit_imports),
    }
    manifest = make_manifest(nodes, decls, inventory, build)
    manifest["project_source_sha256"] = project_inventory
    (HERE / "manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    check_saved(inventory)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"Statement verification failed: {error}", file=sys.stderr)
        sys.exit(1)
