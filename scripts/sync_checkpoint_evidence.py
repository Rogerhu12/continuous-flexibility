"""Route only hash-bound, actually audited checkpoint declarations into the blueprint."""

from __future__ import annotations

import argparse
import json

import check_blueprint as bp


def synchronize(data: dict, routing: dict) -> tuple[dict, dict]:
    included, _ = bp.evidence_sources(data)
    by_id = {node["id"]: node for node in data["nodes"]}
    covered = {(e["file"], e["namespace"], d) for n in data["nodes"]
               for e in n["lean_evidence"] for d in e["declarations"]}
    added = 0
    for path in included:
        relative = path.relative_to(bp.ROOT).as_posix()
        for namespace, declaration in bp.public_theorem_locations(path):
            key = (relative, namespace, declaration)
            if key in covered:
                continue
            exact = relative + "::" + namespace + "." + declaration
            node_id = routing["declaration_nodes"].get(exact, routing["file_nodes"].get(path.stem))
            bp.require(node_id in by_id, f"Audited declaration needs an explicit integration route: {key}")
            node = by_id[node_id]
            entry = next((e for e in node["lean_evidence"] if
                          e["file"] == relative and e["namespace"] == namespace), None)
            if entry is None:
                entry = {"file": relative, "namespace": namespace, "declarations": []}
                node["lean_evidence"].append(entry)
            entry["declarations"].append(declaration)
            covered.add(key)
            added += 1
            if node["status"] in {"planned", "specified"}:
                node["status"] = "partial"
    for node_id, note in routing["progress"].items():
        node = by_id[node_id]
        if not node["lean_evidence"]:
            continue
        progress = node.setdefault("implementation_progress", [])
        if note not in progress:
            progress.append(note)
        # Keep the original expansion contracts unchanged for the frozen refined
        # audit. The live remaining list is separate and is the one rendered.
        node["current_remaining_obligations"] = routing["remaining"][node_id]
    _, stats = bp.validate(data)
    return data, {"new_evidence_declarations": added, **stats}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    data = json.loads(bp.MANIFEST.read_text(encoding="utf-8"))
    data["proof_checkpoint"] = args.checkpoint
    routing = json.loads((bp.BLUEPRINT / "checkpoint-routing.json").read_text(encoding="utf-8"))
    result, report = synchronize(data, routing)
    if args.write:
        bp.MANIFEST.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
