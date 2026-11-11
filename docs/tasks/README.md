# Working on a blueprint node

Each file `docs/tasks/<ID>.md` is one line of work: problem, completion standard, source.
One line works on one branch `line/<ID>` and opens one pull request into `main`.
The rules below are the same for every line.

## Start

Read `AGENTS.md`, `docs/STATUS.md`, your task file, your node file
`src/ContinuousFlexibility/Blueprint/<ID>.lean`, the definition of the statement under
`src/ContinuousFlexibility/Statements/`, the cited manuscript lines, and the existing modules
that already prove parts of it. Search `src/` thoroughly: much may exist. Six nodes were closed
in minutes because a theorem with exactly the node statement was already in the tree.

Work until the completion standard is fully met. Do not stop at a draft or an interim report.
Push often.

## What you edit

- Your node file.
- New files you create. Proofs go in new modules under `src/ContinuousFlexibility/<Area>/`
  with distinctive names; sub-blueprint statements go in `src/ContinuousFlexibility/Blueprint/<ID>/`.
- The root import `src/ContinuousFlexibility.lean`: add your finished, sorry-free modules.
- Existing files of other areas only when the proof needs a change there; say so in the pull request.

## If the node is large

If the node is expected to exceed 10,000 lines of Lean, write a sub-blueprint first:

- the necessary intermediate statements in manuscript order, each a `theorem ... := by sorry`
  with real definitions, in its own file under `Blueprint/<ID>/`, each small enough for one
  line (under 10,000 lines), each with a task file `docs/tasks/<ID>-<name>.md`;
- replace the `sorry` in your node file by a sorry-free proof that assembles the node from those
  statements and the node's hypotheses, and push that first so other lines can take the pieces;
- then prove the sub-statements.

Symmetric cases (the two endpoints, left and right) are one general lemma.

## Building

```bash
lake exe cache get
```

```bash
bash scripts/get_build_cache.sh
```

The second command restores the compiled project modules of `main`, so only your files compile.
Build single targets, never a bare `lake build` in a small sandbox:

```bash
LEAN_NUM_THREADS=2 lake build ContinuousFlexibility.Blueprint.<ID>
```

Check one file without writing artifacts with `lake env lean <file>`. CI builds everything on every
push to a `line/**` branch and on every pull request, and prints the blueprint status.

## Lean

- Toolchain and mathlib are fixed. `Set.mem_setOf_eq` and `push_neg` are deprecated in this mathlib.
- Use plain `import` headers (no `module` keyword) until the module migration is merged.
- Do not raise heartbeat limits; find the slow declaration.

## Final report in the pull request

1. Is `theorem <ID>` sorry-free, and what does `#print axioms` show?
2. If not closed: the sub-statements introduced and which are proved.
3. Any clause of the frozen statement found false or underivable from its hypotheses, quoted exactly.
