# ScalarCalculus

## Problem

The pointwise and finite-rectangle calculus of the height equation: connection, residual, conservation, type correction.

Prove `ContinuousFlexibility.Blueprint.ScalarCalculus` in `src/ContinuousFlexibility/Blueprint/ScalarCalculus.lean`:

```lean
theorem ScalarCalculus : S03CalculusStatement ∧ S04CalculusStatement ∧ S05CalculusStatement
```

## Completion standard

- `theorem ScalarCalculus` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.ScalarCalculus` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses is in the root import and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-readable/03-height-equation.tex` lines 23–189; `paper/flexible-surface-readable/03-height-equation.tex` lines 406–543.
