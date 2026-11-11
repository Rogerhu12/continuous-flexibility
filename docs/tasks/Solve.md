# Solve

## Problem

The coupled inverse, the exact quadratic error, the Nash–Moser iteration, and one solution at a nonzero parameter.

Prove `ContinuousFlexibility.Blueprint.Solve` in `src/ContinuousFlexibility/Blueprint/Solve.lean`:

```lean
theorem Solve (hN08 : N08Statement) (hTame : H01Statement ∧ H02Statement) : PointBranchStatement
```

## Completion standard

- `theorem Solve` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.Solve` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses is in the root import and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-rewrite/09-solving-the-equation.tex` lines 139–242.
