"""Generate blueprint v2 from the archived v1 manifest.

One-off generator, kept for the record. For every node on the path to
`Nonempty FlatAnnularCore` it writes

  src/ContinuousFlexibility/Blueprint/<ID>.lean   theorem <ID> (deps) : <ID>Statement := by sorry
  docs/tasks/<ID>.md                              problem, completion standard, source

and it writes the assembly theorem, which has no `sorry` of its own:

  src/ContinuousFlexibility/Blueprint/Assembly.lean

Existing node files are never overwritten, so a node whose `sorry` has been
replaced by a proof is safe.
"""
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs/archive/blueprint-v1/manifest.json"
BP = ROOT / "src/ContinuousFlexibility/Blueprint"
TASKS = ROOT / "docs/tasks"
GOAL = "N12"
SKIP = {"C00"}  # C00 is the target itself, not an input


def main() -> None:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    nodes = {n["id"]: n for n in manifest["nodes"]}

    closure: set[str] = set()

    def visit(x: str) -> None:
        for d in nodes[x]["dependencies"]:
            if d not in closure and d not in SKIP:
                closure.add(d)
                visit(d)

    visit(GOAL)
    closure.add(GOAL)
    order = [n["id"] for n in manifest["nodes"] if n["id"] in closure]

    BP.mkdir(parents=True, exist_ok=True)
    TASKS.mkdir(parents=True, exist_ok=True)

    rows = []
    for nid in order:
        node = nodes[nid]
        deps = [d for d in node["dependencies"] if d not in SKIP]
        refs = node["paper"]
        tex_lines = sum(r["end"] - r["start"] + 1 for r in refs)
        src = "; ".join(
            f"`{r['file']}` lines {r['start']}–{r['end']}" + (f" (`{r['label']}`)" if r.get("label") else "")
            for r in refs
        )
        hyps = "".join(f" (h{d} : {d}Statement)" for d in deps)
        lean = BP / f"{nid}.lean"
        if not lean.exists():
            lean.write_text(
                "import ContinuousFlexibility.Statements.Milestones\n\n"
                "/-!\n"
                f"# Blueprint node {nid}\n\n"
                f"Source: {src}.\n\n"
                f"Task file: `docs/tasks/{nid}.md`. The statement is frozen; replace the `sorry`.\n"
                "-/\n\n"
                "namespace ContinuousFlexibility.Blueprint\n\n"
                "open ContinuousFlexibility.Statements\n\n"
                f"theorem {nid}{hyps} : {nid}Statement := by\n"
                "  sorry\n\n"
                "end ContinuousFlexibility.Blueprint\n",
                encoding="utf-8",
                newline="\n",
            )
        task = TASKS / f"{nid}.md"
        if not task.exists():
            dep_text = ", ".join(f"`{d}Statement`" for d in deps) if deps else "none"
            task.write_text(
                f"# {nid}\n\n"
                "## Problem\n\n"
                f"Prove `ContinuousFlexibility.Blueprint.{nid}` in "
                f"`src/ContinuousFlexibility/Blueprint/{nid}.lean`: from the hypotheses {dep_text}, "
                f"derive `ContinuousFlexibility.Statements.{nid}Statement`.\n\n"
                f"{node['statement']}\n\n"
                "## Completion standard\n\n"
                f"- `theorem {nid}` has exactly the frozen statement and its proof contains no `sorry`; "
                f"`#print axioms ContinuousFlexibility.Blueprint.{nid}` shows only `propext`, "
                "`Classical.choice`, `Quot.sound`.\n"
                "- Every module the proof uses is in the root import and CI is green.\n"
                "- A weaker, relative or conditional version does not complete the task. If the frozen "
                "statement is false or cannot be derived from its hypotheses, record that in "
                "`docs/STATUS.md` with the exact clause, and repair the statement together with "
                "`Blueprint/Assembly.lean`.\n\n"
                "## Source\n\n"
                f"{src}.\n",
                encoding="utf-8",
                newline="\n",
            )
        rows.append((nid, deps, tex_lines, node["title"]))

    # assembly: compose the nodes in manifest (topological) order
    lines = [f"import ContinuousFlexibility.Blueprint.{nid}" for nid in order]
    lines += [
        "",
        "/-!",
        "# Blueprint assembly",
        "",
        "The blueprint nodes compose to `Nonempty FlatAnnularCore`. This file contains no",
        "`sorry`; the result depends on `sorryAx` exactly through the nodes that are still open.",
        "-/",
        "",
        "namespace ContinuousFlexibility.Blueprint",
        "",
        "open ContinuousFlexibility.Statements",
        "",
        "/-- The analytic existence statement, assembled from the blueprint nodes. -/",
        "theorem flatAnnularCore_nonempty : Nonempty FlatAnnularCore := by",
    ]
    for nid in order:
        deps = [d for d in nodes[nid]["dependencies"] if d not in SKIP]
        args = "".join(f" h{d}" for d in deps)
        lines.append(f"  have h{nid} : {nid}Statement := {nid}{args}")
    lines += [f"  exact h{GOAL}", "", "end ContinuousFlexibility.Blueprint", ""]
    (BP / "Assembly.lean").write_text("\n".join(lines), encoding="utf-8", newline="\n")

    for nid, deps, tex_lines, title in rows:
        print(f"{nid}\t{tex_lines}\t{','.join(deps)}\t{title}")


if __name__ == "__main__":
    main()
