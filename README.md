# ContinuousFlexibility

Lean 4 formalization of the main theorem (`thm:main`) of the manuscript *Smooth isometric bending
of a closed sphere* in `paper/flexible-surface-readable/` (the 62-page version in
`paper/flexible-surface-rewrite/` has the same theorems): there is a smooth, periodic family of
isometric embeddings of the sphere in `ℝ³` whose images are not all congruent.

The theorem is proved: `FlexibleSphere.exists_closedBending` (`src/Solution/FlexibleSphereSolution.lean`)
has no `sorry` and depends only on `propext`, `Classical.choice` and `Quot.sound`. The statement is
the Mathlib-only Challenge `src/Challenge/FlexibleSphereChallenge.lean`; `comparator.json` pairs the
two. Current state and numbers: [docs/STATUS.md](docs/STATUS.md).
Working rules: [AGENTS.md](AGENTS.md).

## Build

Lean `leanprover/lean4:v4.35.0-rc3`, mathlib at the revision in `lake-manifest.json`.

```bash
lake exe cache get
```

```bash
LEAN_NUM_THREADS=4 lake build
```

The default targets are the library, the axiom audit, the Challenge and the Solution.

## Layout

- `src/` — Lean sources; `src/Challenge/` and `src/Solution/` hold the statement and its proof.
- `docs/` — status ledger, task files, archive of the earlier workflow.
- `paper/` — the manuscript.
- `scripts/` — the root-import generator and `BlueprintStatus.lean`.
