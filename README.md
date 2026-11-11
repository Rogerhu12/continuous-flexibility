# ContinuousFlexibility

Lean 4 formalization of the main theorem of the manuscript in `paper/flexible-surface-rewrite/`:
there is a smooth, periodic family of isometric embeddings of the sphere in `ℝ³` whose images are
not all congruent.

The theorem is **not yet proved**. Current state, numbers and next steps: [docs/STATUS.md](docs/STATUS.md).
Working rules: [AGENTS.md](AGENTS.md).

## Build

Lean `leanprover/lean4:v4.35.0-rc3`, mathlib at the revision in `lake-manifest.json`.

```bash
lake exe cache get
```

```bash
LEAN_NUM_THREADS=4 lake build ContinuousFlexibility
```

## Layout

- `src/` — Lean sources.
- `docs/` — status ledger, task files, archive of the earlier workflow.
- `paper/` — the manuscript.
- `vendor/` — third-party code.
