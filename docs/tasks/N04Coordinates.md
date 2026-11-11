# N04Coordinates

## Problem

The uniform bounds of the potential and of the divided differences, and the conversion of sources (rest of Proposition 7.8).

Prove `ContinuousFlexibility.Blueprint.N04Coordinates` in `src/ContinuousFlexibility/Blueprint/N04Coordinates.lean`:

```lean
theorem N04Coordinates (hN04b : N04bStatement) : N04cStatement
```

## Completion standard

- `theorem N04Coordinates` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.N04Coordinates` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses compiles in CI (the root import is generated) and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1497–1725.
