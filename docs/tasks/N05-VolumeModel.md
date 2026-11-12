# N05-VolumeModel

## Problem

Prove `ContinuousFlexibility.Blueprint.N05VolumeModel` in
`src/ContinuousFlexibility/Blueprint/N05/VolumeModel.lean`: construct
`VolumeModelData` satisfying the literal `IsVolumeModel` specification.

The level carrier is the actual finite angular weak derivative graph in
canonical volume L². Prove its closedness, uniqueness of weak derivatives,
injectivity of the forget map and the exact weight formula.

## Completion standard

- The exact theorem and all its dependencies compile in CI.
- The axiom audit contains only `propext`, `Classical.choice` and `Quot.sound`.
- An arbitrary Hilbert scale or an assumed graph closure is insufficient.

## Source

`paper/flexible-surface-readable/08-stable-inverse.tex` lines 34--74.
