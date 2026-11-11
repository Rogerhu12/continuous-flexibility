# Working on a blueprint node

Each file `docs/tasks/<Node>.md` is one line of work: problem, completion standard, source.
A `Tool-*` task has no blueprint node: its Lean statement follows the manuscript lemma it cites.
Line numbers refer to the readable manuscript in `paper/flexible-surface-readable/`; older Lean files
cite the 62-page version in `paper/flexible-surface-rewrite/`, which has the same labels.
One line works on one branch `line/<Node>` and opens one pull request into `main`.
The rules below are the same for every line.

## Start

Read `AGENTS.md`, `docs/STATUS.md`, your task file, your node file
`src/ContinuousFlexibility/Blueprint/<Node>.lean`, the definition of the statement under
`src/ContinuousFlexibility/Statements/` or in `Blueprint/Statements.lean`, the cited manuscript lines, and the existing modules
that already prove parts of it. Search `src/` thoroughly: much may exist. Six nodes were closed
in minutes because a theorem with exactly the node statement was already in the tree.

Work until the completion standard is fully met. Do not stop at a draft or an interim report.
Push often.

## What you edit

- Your node file.
- New files you create. Proofs go in new modules under `src/ContinuousFlexibility/<Area>/`
  with distinctive names; sub-blueprint statements go in `src/ContinuousFlexibility/Blueprint/<Node>/`.
- The root import `src/ContinuousFlexibility.lean`: add your finished, sorry-free modules.
- Existing files of other areas only when the proof needs a change there; say so in the pull request.

## If the node is large

A line normally carries a whole node; 20,000–30,000 lines of Lean in one line is expected.
Only if the node will clearly go well beyond 30,000 lines, write a sub-blueprint first:

- the necessary intermediate statements in manuscript order, each a `theorem ... := by sorry`
  with real definitions, in its own file under `Blueprint/<Node>/`, each of a size one line can
  carry (up to about 30,000 lines), each with a task file `docs/tasks/<Node>-<name>.md`;
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
LEAN_NUM_THREADS=2 lake build ContinuousFlexibility.Blueprint.<Node>
```

Check one file without writing artifacts with `lake env lean <file>`.

## If the sandbox cannot compile, use CI

Do not spend time fighting the sandbox. If a compile runs out of memory, is killed, or takes more
than a few minutes for one file, stop compiling locally: write the code, push, and read the result
of CI. That loop always works.

- CI builds everything on every push to a `line/**` branch and on every pull request, prints the
  blueprint status, and takes about 5 minutes with the cache. A newer push cancels the older run.
- Find the run of your branch and its errors:

```bash
gh run list --branch line/<Node> --limit 3
```

```bash
gh run view <run-id> --log-failed
```

- The step "Build every library" prints every `error:` line with the following 60 lines; the full
  log is the artifact `build-log`.
- Push small, complete steps (one file or one lemma group at a time), so that one CI round tells
  you about one change. Do not pile up thousands of unchecked lines before the first push.

## Lean

- Toolchain and mathlib are fixed. `Set.mem_setOf_eq` and `push_neg` are deprecated in this mathlib.
- Use plain `import` headers (no `module` keyword) until the module migration is merged.
- Do not raise heartbeat limits; find the slow declaration.

## Final report in the pull request

1. Is `theorem <Node>` sorry-free, and what does `#print axioms` show?
2. If not closed: the sub-statements introduced and which are proved.
3. Any clause of the frozen statement found false or underivable from its hypotheses, quoted exactly.
