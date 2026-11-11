# Solve

## Problem

The Nash–Moser iteration with quadratic error (Theorem 9.4) applied to the coupled system: one solution at a nonzero parameter.

Prove `ContinuousFlexibility.Blueprint.Solve` in `src/ContinuousFlexibility/Blueprint/Solve.lean`:

```lean
theorem Solve (hN10 : N10Statement) (hTame : H01Statement ∧ H02Statement) : PointBranchStatement
```

## Completion standard

- `theorem Solve` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.Solve` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses compiles in CI (the root import is generated) and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-readable/09-solving-the-equation.tex` lines 251–413.
