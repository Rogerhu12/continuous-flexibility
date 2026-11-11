# Tame

## Problem

Tame calculus on projective limits of Banach scales and Hamilton's theorem on families of inverses.

Prove `ContinuousFlexibility.Blueprint.Tame` in `src/ContinuousFlexibility/Blueprint/Tame.lean`:

```lean
theorem Tame : H01Statement ∧ H02Statement
```

## Completion standard

- `theorem Tame` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.Tame` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses is in the root import and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-rewrite/07-fixed-geometry.tex` lines 102–150; `paper/flexible-surface-rewrite/08-stable-inverse.tex` lines 523–550.
