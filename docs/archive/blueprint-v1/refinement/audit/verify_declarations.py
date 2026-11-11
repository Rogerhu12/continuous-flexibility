"""Resolve every proposed completion's exact constants in the rebuilt snapshot."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
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
    snapshot = Path(read(HERE / "source-snapshot.json")["snapshot_root"])
    builds = read(HERE / "build-results.json")
    assert builds.get("finished_at_utc"), "Wait for owned build session completion"
    assert builds["axiom_audit"]["exit_code"] == 0
    proposed = [r for name in REVIEW_FILES for r in read(HERE / name)["reviews"]
                if r["status"] == "complete"]
    supported = [r for r in proposed if all(builds["modules"].get(e["file"][:-5].replace("/", "."), {}).get("status") == "passed"
                                           for e in r["evidence"])]
    names = sorted({name for r in supported for e in r["evidence"] for name in e["declarations"]})
    origins = sorted({(name, e["file"][:-5].replace("/", ".")) for r in supported for e in r["evidence"] for name in e["declarations"]})
    imports = [m for m, r in builds["modules"].items() if r["status"] == "passed"]
    artifacts = {}
    for module in imports:
        path = Path(builds["isolated_output"]) / Path(*module.split("."))
        actual = digest(Path(str(path) + ".olean"))
        assert actual == builds["modules"][module]["olean_sha256"], module
        artifacts[module] = actual
    source = HERE / "DeclarationEvidence.lean"
    content = "\n".join("import " + n for n in imports) + r'''
import Lean.Util.CollectAxioms
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
open Lean in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let projectOwner := match env.getModuleIdxFor? name with
      | some idx => (`ContinuousFlexibility).isPrefixOf env.allImportedModuleNames[idx.toNat]!
      | none => false
    if (`ContinuousFlexibility).isPrefixOf name || projectOwner then
      if info.isUnsafe then
        throwError "Unsafe project declaration: {name}"
      match info with
      | .axiomInfo _ => throwError "Project axiom declared: {name}"
      | _ => pure ()
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations checked"
  logInfo m!"Owner unsafe/axiom audit passed for {checked} declarations"
''' + "\nopen Lean in\nrun_cmd do\n  let env ← getEnv\n  let expected : List (Name × Name) := [" + ", ".join(f"(`{name}, `{module})" for name, module in origins) + "]\n" + r'''
  for (name, owner) in expected do
    let some idx := env.getModuleIdxFor? name
      | throwError "Declaration has no imported owner: {name}"
    unless env.allImportedModuleNames[idx.toNat]! == owner do
      throwError "Wrong evidence module for {name}; expected {owner}, got {env.allImportedModuleNames[idx.toNat]!}"
set_option pp.fullNames true
set_option pp.universes false
''' + "\n".join("#check " + name for name in names) + "\n"
    source.write_text(content, encoding="utf-8")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "4"
    env["PYTHONUTF8"] = "1"
    inherited = json.loads(subprocess.run(
        ["lake", "env", "python", "-X", "utf8", "-c",
         "import os,json; print(json.dumps({k:os.environ.get(k,'') for k in ['LEAN_PATH','PATH']}))"],
        cwd=ROOT, env=env, capture_output=True, text=True, encoding="utf-8", check=True,
    ).stdout)
    shared = str((ROOT / ".lake/build/lib/lean").resolve()).casefold()
    paths = [p for p in inherited["LEAN_PATH"].split(os.pathsep)
             if p and str(Path(p).resolve()).casefold() != shared]
    env["LEAN_PATH"] = os.pathsep.join([builds["isolated_output"]] + paths)
    env["PATH"] = inherited["PATH"]
    lean = builds["modules"][imports[0]]["command"][0]
    command = [lean, str(source), "-R", str(ROOT), "-j", "4"]
    result = subprocess.run(command, cwd=snapshot, env=env, capture_output=True,
                            text=True, encoding="utf-8", errors="replace")
    log = HERE / "DeclarationEvidence.log"
    log.write_text(result.stdout + result.stderr, encoding="utf-8")
    for module in imports:
        path = Path(builds["isolated_output"]) / Path(*module.split("."))
        assert digest(Path(str(path) + ".olean")) == artifacts[module], module
    report = {"schema_version": 1, "exit_code": result.returncode, "command": command,
              "snapshot": str(snapshot), "build_report_sha256": digest(HERE / "build-results.json"),
              "module_olean_sha256": artifacts,
              "resolved_names": names if result.returncode == 0 else [],
              "attempted_names": names, "supported_candidate_ids": [r["id"] for r in supported],
              "declaration_owners": {name: module for name, module in origins},
              "source": source.relative_to(ROOT).as_posix(), "source_sha256": digest(source),
              "log": log.relative_to(ROOT).as_posix(), "log_sha256": digest(log),
              "owner_unsafe_audit_passed": result.returncode == 0 and "Owner unsafe/axiom audit passed" in result.stdout}
    (HERE / "declaration-check.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print({"exit_code": result.returncode, "names": len(names), "candidate_tasks": len(supported)})
    if result.returncode:
        print(result.stdout[-14000:] + result.stderr[-3000:])
        raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
