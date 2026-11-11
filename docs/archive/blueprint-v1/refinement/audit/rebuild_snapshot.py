"""Recompile the immutable source snapshot without touching shared build outputs."""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from datetime import datetime, timezone
from graphlib import TopologicalSorter
from pathlib import Path


AUDIT = Path(__file__).resolve().parent
ROOT = AUDIT.parents[2]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    metadata = json.loads((AUDIT / "source-snapshot.json").read_text(encoding="utf-8"))
    snapshot = Path(metadata["snapshot_root"])
    output = snapshot / "build/lib/lean"
    logs = AUDIT / "build-logs"
    output.mkdir(parents=True, exist_ok=True)
    logs.mkdir(exist_ok=True)
    for name, expected in metadata["files"].items():
        assert digest(snapshot / name) == expected, name
    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = "4"
    environment["PYTHONUTF8"] = "1"
    raw = subprocess.run(
        ["lake", "env", "python", "-X", "utf8", "-c",
         "import os,json; print(json.dumps({k:os.environ.get(k,'') for k in ['LEAN_PATH','PATH']}))"],
        cwd=ROOT, env=environment, capture_output=True, text=True, encoding="utf-8", check=True,
    )
    inherited = json.loads(raw.stdout)
    shared_output = str((ROOT / ".lake/build/lib/lean").resolve()).casefold()
    paths = [p for p in inherited["LEAN_PATH"].split(os.pathsep)
             if p and str(Path(p).resolve()).casefold() != shared_output]
    environment["LEAN_PATH"] = os.pathsep.join([str(output)] + paths)
    environment["PATH"] = inherited["PATH"]
    prefix = subprocess.run(["lean", "--print-prefix"], cwd=snapshot, env=environment,
                            capture_output=True, text=True, encoding="utf-8", check=True).stdout.strip()
    lean = Path(prefix) / "bin/lean.exe"
    version = subprocess.run([str(lean), "--version"], cwd=snapshot, env=environment,
                             capture_output=True, text=True, encoding="utf-8", check=True).stdout.strip()
    modules = {Path(name).with_suffix("").as_posix().replace("/", "."): snapshot / name
               for name in metadata["files"] if name.endswith(".lean")}
    graph = {}
    for module, path in modules.items():
        imports = re.findall(r"^import\s+(\S+)\s*$", path.read_text(encoding="utf-8"), re.M)
        graph[module] = [name for name in imports if name in modules]
    report = {"schema_version": 1, "snapshot": str(snapshot), "lean_version": version,
              "lean_num_threads": 4, "isolated_output": str(output),
              "started_at_utc": datetime.now(timezone.utc).isoformat(), "modules": {}}
    failed = set()
    order = list(TopologicalSorter(graph).static_order())
    for index, name in enumerate(order, 1):
        source = modules[name]
        if any(dep in failed for dep in graph[name]):
            failed.add(name)
            report["modules"][name] = {"status": "blocked_by_failed_import", "source_sha256": digest(source)}
            continue
        target = output / Path(*name.split("."))
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), str(source), "-R", str(snapshot), "-o", str(target) + ".olean",
                   "-i", str(target) + ".ilean", "-j", "4",
                   "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]
        result = subprocess.run(command, cwd=snapshot, env=environment, capture_output=True,
                                text=True, encoding="utf-8", errors="replace")
        log = logs / (name + ".log")
        log.write_text(result.stdout + result.stderr, encoding="utf-8")
        record = {"status": "passed" if result.returncode == 0 else "failed", "exit_code": result.returncode,
                  "source_sha256": digest(source), "log": log.relative_to(ROOT).as_posix(),
                  "log_sha256": digest(log), "command": command}
        if result.returncode == 0:
            record["olean_sha256"] = digest(Path(str(target) + ".olean"))
        else:
            failed.add(name)
        report["modules"][name] = record
        (AUDIT / "build-results.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        if index % 5 == 0 or result.returncode:
            print(f"{index}/{len(order)} {name}: {record['status']}", flush=True)
            if result.returncode:
                print((result.stdout + result.stderr)[-2500:], flush=True)

    successful = [name for name in order if name not in failed]
    audit_source = snapshot / "CompletionAudit.lean"
    audit_source.write_text("\n".join("import " + n for n in successful) + "\n" + r'''
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut declarations : Nat := 0
  for (name, info) in env.constants.toList do
    let projectOwner := match env.getModuleIdxFor? name with
      | some idx => (`ContinuousFlexibility).isPrefixOf env.allImportedModuleNames[idx.toNat]!
      | none => false
    if (`ContinuousFlexibility).isPrefixOf name || projectOwner then
      declarations := declarations + 1
      match info with
      | .thmInfo _ => checked := checked + 1
      | .axiomInfo _ => throwError "Project axiom declared: {name}"
      | _ => pure ()
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom {ax} in {name}"
  if checked == 0 then
    throwError "No project theorems were found"
  logInfo m!"Snapshot axiom audit passed for {declarations} project declarations ({checked} theorems)"
''', encoding="utf-8")
    result = subprocess.run([str(lean), str(audit_source), "-R", str(snapshot), "-j", "4"],
                            cwd=snapshot, env=environment, capture_output=True, text=True,
                            encoding="utf-8", errors="replace")
    log = logs / "CompletionAudit.log"
    log.write_text(result.stdout + result.stderr, encoding="utf-8")
    report["axiom_audit"] = {"exit_code": result.returncode, "log": log.relative_to(ROOT).as_posix(),
                              "log_sha256": digest(log), "source_sha256": digest(audit_source),
                              "modules": successful, "allowlist": ["propext", "Classical.choice", "Quot.sound"]}
    report["finished_at_utc"] = datetime.now(timezone.utc).isoformat()
    (AUDIT / "build-results.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(result.stdout + result.stderr, flush=True)
    print(json.dumps({"modules": len(order), "passed": len(successful), "failed": sorted(failed),
                      "axiom_audit_exit_code": result.returncode}), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
