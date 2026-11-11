# Spaces

## Problem

The weighted height, source and circle spaces with their tame structure, and smooth flat extension of their elements (Lemma 7.4).

Prove `ContinuousFlexibility.Blueprint.Spaces` in `src/ContinuousFlexibility/Blueprint/Spaces.lean`:

```lean
theorem Spaces (hW01 : W01Statement) (hTame : H01Statement ∧ H02Statement) : W02Statement ∧ W03Statement
```

## Completion standard

- `theorem Spaces` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.Spaces` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses compiles in CI (the root import is generated) and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 108–237; `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 399–506.
