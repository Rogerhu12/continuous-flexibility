#!/usr/bin/env python3
"""Finite, serial Lean build runner. No source edits, cache fetches, or retries."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([A-Za-z0-9_.]+)", re.M)
MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")
LOG_DIR = ROOT / "scratch/serial-build-logs"
IMPORTS_CACHE = {}


def imports(text):
    """Ignore nested Lean comments and string literals before reading imports."""
    output, depth, string, escaped, index = [], 0, False, False, 0
    while index < len(text):
        char, pair = text[index], text[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                string = False
            index += 1
        elif pair == "/-":
            depth, index = 1, index + 2
        elif pair == "--":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        else:
            if char == '"':
                string = True
                output.append(" ")
            else:
                output.append(char)
            index += 1
    return IMPORT.findall("".join(output))


def file_imports(path):
    stat = path.stat()
    stamp = (stat.st_mtime_ns, stat.st_size)
    cached = IMPORTS_CACHE.get(path)
    if cached is None or cached[0] != stamp:
        cached = (stamp, imports(path.read_text(encoding="utf-8-sig")))
        IMPORTS_CACHE[path] = cached
    return cached[1]


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def source_path(module):
    if not MODULE.fullmatch(module):
        raise ValueError(f"Invalid module: {module}")
    return ROOT / (module.replace(".", "/") + ".lean")


def snapshot(module):
    """Hash every transitive project import and the fixed dependency locks."""
    pending, result = [module], {}
    while pending:
        name = pending.pop()
        if name in result:
            continue
        path = source_path(name)
        result[name] = digest(path)
        pending.extend(x for x in file_imports(path)
                       if x.startswith("ContinuousFlexibility."))
    for name in ("lean-toolchain", "lake-manifest.json"):
        result["@" + name] = digest(ROOT / name)
    encoded = json.dumps(result, sort_keys=True).encode("utf-8")
    return result, hashlib.sha256(encoded).hexdigest().upper()


def missing_mathlib(module):
    """Refuse uncached owning-source closures instead of downloading/building them."""
    pending, seen, missing = [module], set(), []
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if name == "ContinuousFlexibility" or name.startswith("ContinuousFlexibility."):
            path = source_path(name)
        elif name == "Mathlib" or name.startswith("Mathlib."):
            relative = name.replace(".", "/")
            path = ROOT / ".lake/packages/mathlib" / (relative + ".lean")
            olean = ROOT / ".lake/packages/mathlib/.lake/build/lib/lean" / (relative + ".olean")
            if not olean.is_file():
                missing.append(name)
        else:
            continue
        if path.is_file():
            pending.extend(file_imports(path))
    return sorted(set(missing))


def save(path, data):
    data["updated_at"] = now()
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n",
                         encoding="utf-8")
    temporary.replace(path)


def load_ready(path, targets):
    """Accept owner-published READY only within that owner's registered scopes."""
    workers = {w["worker"]: w for w in
               read_json(ROOT / "coordination/active-workers.json")["workers"]}
    files = sorted(path.glob("*.json")) if path.is_dir() else [path]
    by_module, owners = {}, {}
    def permitted(relative, scopes):
        relative = relative.replace("\\", "/").casefold()
        return any(relative.startswith(s.replace("\\", "/").casefold())
                   if s.endswith(("/", "\\")) else
                   relative == s.replace("\\", "/").casefold() for s in scopes)
    for file in files:
        publication = read_json(file)
        owner = publication.get("source_owner")
        if owner not in workers:
            raise ValueError(f"Unregistered READY source_owner in {file}: {owner}")
        worker = workers[owner]
        scopes = worker.get("scope", [])
        relative = file.resolve().relative_to(ROOT).as_posix()
        if not permitted(relative, scopes):
            raise ValueError(f"READY publication outside owner scope: {relative}")
        source_scopes = scopes + worker.get("frozen_deliveries", [])
        for module, sha in publication["modules"].items():
            source = source_path(module).relative_to(ROOT).as_posix()
            if not permitted(source, source_scopes):
                raise ValueError(f"READY source outside owner scope: {owner}: {source}")
            if module in owners and owners[module] != owner:
                raise ValueError(f"Conflicting READY source owners: {module}")
            if not re.fullmatch(r"[0-9a-fA-F]{64}", sha):
                raise ValueError(f"Invalid SHA256 in READY: {module}")
            by_module[module], owners[module] = sha.upper(), owner
    for target in targets:
        module = target["module"]
        if module in owners and owners[module] != target["source_owner"]:
            raise ValueError(f"Queue/READY source_owner mismatch: {module}")
    return by_module


def refresh(data):
    """Preserve historical terminal outcomes; invalidate obsolete current certificates."""
    observed = {}
    for record in data.get("records", []):
        if record.get("status") != "stable_pass":
            continue
        try:
            module = record["module"]
            if module not in observed:
                inputs, signature = snapshot(module)
                observed[module] = (inputs[module], signature)
            direct, current = observed[module]
            if direct != record.get("end_hash", "").upper():
                reason = "source changed after build"
            elif record.get("dependency_signature") != current:
                reason = "project dependency signature changed or was not recorded"
            else:
                record["current_status"] = "stable_pass"
                continue
            record["current_status"] = "stale"
            record["invalidation_reason"] = reason
        except OSError as exc:
            record["current_status"] = "stale"
            record["invalidation_reason"] = str(exc)


def audited_checkpoint_inputs():
    """Read the integration build certificate for the exact audited source closure."""
    registry = read_json(ROOT / "coordination/active-workers.json")
    checkpoint_path = registry.get("latest_verified_checkpoint")
    if not checkpoint_path:
        return {}
    checkpoint = read_json(ROOT / checkpoint_path)
    build = checkpoint["build"]
    sources = checkpoint["sources"]
    if (build.get("terminal_exit_code") != 0 or build.get("warnings") != 0
        or build.get("source_and_context_drift") is not False
        or not build.get("audit_declarations")
        or not {"ContinuousFlexibility.lean", "AxiomAudit.lean"} <= sources.keys()):
        return {}
    context = checkpoint["context_hashes"]
    if any(digest(ROOT / name) != expected.upper() for name, expected in context.items()):
        return {}
    inputs = {name.removesuffix(".lean").replace("/", "."): source["sha256"].upper()
              for name, source in sources.items()}
    inputs.update({"@" + name: context[name].upper()
                   for name in ("lean-toolchain", "lake-manifest.json")})
    return inputs


def current_pass(data, module, audited_inputs):
    records = [r for r in data.get("records", []) if r.get("module") == module]
    if records and records[-1].get("current_status", records[-1].get("status")) == "stable_pass":
        return True
    if module not in audited_inputs:
        return False
    inputs, _ = snapshot(module)
    return all(audited_inputs.get(name) == value for name, value in inputs.items())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queue", type=Path, default=ROOT / "coordination/serial-build-queue.json")
    parser.add_argument("--ready", type=Path, default=ROOT / "coordination/ready")
    parser.add_argument("--results", type=Path, default=ROOT / "coordination/serial-build-results.json")
    parser.add_argument("--modules", nargs="+", help="Finite ordered subset of queue targets")
    parser.add_argument("--round", type=int, default=4)
    parser.add_argument("--retry-unchanged", action="store_true",
                        help="Explicitly retry a previously failed identical source/dependency signature")
    parser.add_argument("--dry-run", action="store_true", help="Read/check only; no results or builds")
    args = parser.parse_args()
    queue = read_json(args.queue)["targets"]
    by_name = {target["module"]: target for target in queue}
    selected = [by_name[name] for name in args.modules] if args.modules else queue
    ready = load_ready(args.ready, selected)
    data = read_json(args.results)
    audited_inputs = audited_checkpoint_inputs()
    if data.get("current_build") and not args.dry_run:
        parser.error("results already contain an unfinalized current_build")
    if args.dry_run:
        for target in selected:
            module = target["module"]
            _, signature = snapshot(module)
            print(json.dumps({"module": module, "ready_matches":
                ready.get(module) == digest(source_path(module)),
                "dependency_signature": signature,
                "missing_mathlib": missing_mathlib(module)}, ensure_ascii=False), flush=True)
        return 0
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    lock = LOG_DIR / "runner.lock"
    try:
        lock_fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        parser.error("runner.lock exists; its owner must confirm terminal before removal")
    runner_id = str(uuid.uuid4())
    os.write(lock_fd, json.dumps({"runner_id": runner_id, "pid": os.getpid(),
                                 "started_at": now()}).encode())
    os.close(lock_fd)
    active_process = None
    try:
        refresh(data)
        data["selected_order"] = list(dict.fromkeys(
            data.get("selected_order", []) + [t["module"] for t in selected]))
        data["runner_execution"] = {"id": runner_id, "pid": os.getpid(),
                                   "started_at": now(), "finite": True}
        save(args.results, data)
        for target in selected:
            module = target["module"]
            refresh(data)
            ready = load_ready(args.ready, selected)
            path = source_path(module)
            if module not in ready or not path.is_file():
                record = {**target, "source": str(path.relative_to(ROOT)),
                          "round": args.round, "runner_id": runner_id,
                          "started_at": now(), "status": "pending_ready",
                          "reason": "source not published READY or file not yet present",
                          "start_hash": digest(path) if path.is_file() else None,
                          "exit_code": None}
                data.setdefault("records", []).append(record)
                save(args.results, data)
                print("SERIAL_RESULT " + json.dumps(record, ensure_ascii=False), flush=True)
                continue
            prerequisites = list(target.get("requires", []))
            if target.get("after"):
                prerequisites.append(target["after"])
            inputs, signature = snapshot(module)
            start_hash = inputs[module]
            if current_pass(data, module, audited_inputs):
                print("SERIAL_CURRENT_PASS " + module, flush=True)
                continue
            record = {**target, "source": str(source_path(module).relative_to(ROOT)),
                      "round": args.round, "runner_id": runner_id,
                      "started_at": now(), "start_hash": start_hash,
                      "dependency_start_signature": signature,
                      "project_inputs_start": inputs}
            failures = [r for r in data.get("records", [])
                        if r.get("module") == module and r.get("status") == "failed"]
            previous = failures[-1] if failures else {}
            unchanged_failure = (previous.get("start_hash") == start_hash and
                previous.get("dependency_signature", previous.get("dependency_end_signature")) == signature)
            if ready.get(module) != start_hash:
                record.update(status="pending_ready", reason="explicit READY hash missing/mismatched")
            elif unchanged_failure and not args.retry_unchanged:
                record.update(status="pending_source_fix", reason="identical source/dependency already failed")
            elif any(not current_pass(data, p, audited_inputs) for p in prerequisites):
                record.update(status="pending_dependency", reason="requires current stable PASS",
                              unmet=[p for p in prerequisites if not current_pass(data, p, audited_inputs)])
            elif missing := missing_mathlib(module):
                record.update(status="missing_dependency", missing_mathlib=missing)
            else:
                log = LOG_DIR / f"round{args.round}-{module.replace('.', '_')}-{runner_id[:8]}.log"
                env = os.environ.copy()
                env["LEAN_NUM_THREADS"] = "4"
                command = ["lake", "--wfail", "build", module]
                data["current_build"] = {**record, "command": command,
                                         "log": str(log.relative_to(ROOT))}
                save(args.results, data)
                output = []
                with log.open("w", encoding="utf-8") as stream:
                    stream.write(json.dumps(data["current_build"], ensure_ascii=False) + "\n\n")
                    stream.flush()
                    process = subprocess.Popen(command, cwd=ROOT, env=env,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                        text=True, encoding="utf-8", errors="replace")
                    active_process = process
                    data["current_build"]["child_pid"] = process.pid
                    save(args.results, data)
                    assert process.stdout is not None
                    for line in process.stdout:
                        if line.startswith("trace:") or re.match(r"\s*\.> LEAN_PATH=", line):
                            continue
                        output.append(line)
                        stream.write(line)
                        stream.flush()
                        print(line, end="", flush=True)
                    exit_code = process.wait()
                    active_process = None
                    end_inputs, end_signature = snapshot(module)
                    record.update(exit_code=exit_code, child_pid=process.pid,
                        ended_at=now(), end_hash=end_inputs[module],
                        dependency_signature=end_signature, project_inputs_end=end_inputs,
                        log=str(log.relative_to(ROOT)))
                    record["status"] = ("source_changed" if end_signature != signature else
                                        "stable_pass" if exit_code == 0 else "failed")
                    record["current_status"] = record["status"]
                    record["errors"] = [line.rstrip() for line in output
                                        if re.match(r"^(error|warning):", line)]
                    stream.write("\nTERMINAL " + json.dumps(record, ensure_ascii=False) + "\n")
                data["current_build"] = None
            data.setdefault("records", []).append(record)
            save(args.results, data)
            print("SERIAL_RESULT " + json.dumps({k: record.get(k) for k in
                  ("module", "status", "exit_code", "start_hash", "end_hash", "log")},
                  ensure_ascii=False), flush=True)
        data["runner_execution"]["ended_at"] = now()
        refresh(data)
        save(args.results, data)
        return 0 if all(current_pass(data, t["module"], audited_inputs) for t in selected) else 1
    finally:
        if active_process is not None and active_process.poll() is None:
            # Keep the executor's tool session alive until its child really terminates.
            active_process.wait()
        # No automatic recovery of another execution's lock or current_build.
        lock.unlink()


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    raise SystemExit(main())

