# N04Transmission

## Problem

Piecewise smooth solutions with matching value and conormal derivative have matching jets.

Prove `ContinuousFlexibility.Blueprint.N04Transmission` in `src/ContinuousFlexibility/Blueprint/N04Transmission.lean`:

```lean
theorem N04Transmission : PhysicalTransmissionTarget
```

## Completion standard

- `theorem N04Transmission` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.N04Transmission` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses is in the root import and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-rewrite/07-fixed-geometry.tex` lines 706–715.
