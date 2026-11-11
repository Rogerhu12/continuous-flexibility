# N04Coordinates

## Problem

Canonical coordinates on the negative and positive pieces, the Airy form, the cut condition and the source conversion.

Prove `ContinuousFlexibility.Blueprint.N04Coordinates` in `src/ContinuousFlexibility/Blueprint/N04Coordinates.lean`:

```lean
theorem N04Coordinates (hN03 : N03Statement) : N04cStatement
```

## Completion standard

- `theorem N04Coordinates` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.N04Coordinates` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses is in the root import and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-rewrite/07-fixed-geometry.tex` lines 462–494; `paper/flexible-surface-rewrite/07-fixed-geometry.tex` lines 551–704.
