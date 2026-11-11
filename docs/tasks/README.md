# Working on a blueprint node

Each file `docs/tasks/<ID>.md` is one line of work: problem, completion standard, source.
The rules below are the same for every line.

## Start

Read `AGENTS.md`, `docs/STATUS.md`, your task file, your node file
`src/ContinuousFlexibility/Blueprint/<ID>.lean`, the definition of the statement under
`src/ContinuousFlexibility/Statements/`, the cited manuscript lines, and the existing modules
that already prove parts of it. Search `src/` thoroughly: much may exist.

Work until the completion standard is fully met. Do not stop at a draft or an interim report.

## What you may edit

- Your node file.
- New files you create. Proofs go in new modules under `src/ContinuousFlexibility/<Area>/`
  with distinctive names; sub-blueprint statements go in `src/ContinuousFlexibility/Blueprint/<ID>/`.
- Nothing else. Other lines work in the same tree at the same time. Do not edit files you did
  not create, `docs/STATUS.md`, the lakefile or the root import, and do not run git commands
  that change the repository; the lead commits.

## If the node is large

If the node is expected to exceed 10,000 lines of Lean, or clearly cannot be closed in one
session, write a sub-blueprint first:

- the necessary intermediate statements in manuscript order, each a `theorem … := by sorry`
  with real definitions, in its own file under `Blueprint/<ID>/`, each small enough for one
  worker (under 10,000 lines);
- then replace the `sorry` in your node file by a sorry-free proof that assembles the node from
  those statements and the node's hypotheses;
- then prove as many of the sub-statements as you can.

Symmetric cases (the two endpoints, left and right) are one general lemma.

## Lean

- Toolchain and mathlib are fixed. Mathlib sources are in `.lake/packages/mathlib`; grep for
  exact names. Not every mathlib module has a compiled olean locally: avoid one that fails to
  import. `Set.mem_setOf_eq` and `push_neg` are deprecated in this mathlib.
- Use plain `import` headers (no `module` keyword) until the module migration is done.
- Check a file without writing artifacts: `LEAN_NUM_THREADS=4 lake env lean <file>`.
- Make a new module importable by building exactly it: `LEAN_NUM_THREADS=4 lake build <Module.Name>`.
  Never run a bare `lake build`.
- The machine has little free memory and many lines share it: one compile at a time, think
  before compiling, and retry if a compile dies for lack of memory.

## Final report (at most 250 words)

1. Is `theorem <ID>` sorry-free now, and what does `#print axioms` show?
2. Files created.
3. If not closed: the sub-statements introduced (name and one line each) and which are proved.
4. Any clause of the frozen statement found false or underivable from its hypotheses, quoted exactly.
