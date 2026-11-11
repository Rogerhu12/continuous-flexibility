# ScalarWeighted

## Problem

The same three statements on the weighted function spaces, up to the flat endpoints.

Prove `ContinuousFlexibility.Blueprint.ScalarWeighted` in `src/ContinuousFlexibility/Blueprint/ScalarWeighted.lean`:

```lean
theorem ScalarWeighted : S03WeightedStatement ∧ S04WeightedStatement ∧ S05WeightedStatement
```

## Completion standard

- `theorem ScalarWeighted` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.ScalarWeighted` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses is in the root import and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-readable/03-height-equation.tex` lines 406–543; `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 108–506.
