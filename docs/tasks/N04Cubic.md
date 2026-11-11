# N04Cubic

## Problem

Division by y³ of a function vanishing to third order, in L² with three derivatives lost.

Prove `ContinuousFlexibility.Blueprint.N04Cubic` in `src/ContinuousFlexibility/Blueprint/N04Cubic.lean`:

```lean
theorem N04Cubic : CubicDivisionTarget
```

## Completion standard

- `theorem N04Cubic` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.N04Cubic` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses is in the root import and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-rewrite/07-fixed-geometry.tex` lines 676–690.
