# N04Realization-SourceColumns

## Problem

Prove `ContinuousFlexibility.Blueprint.N04RealizationSourceColumns` in
`src/ContinuousFlexibility/Blueprint/N04Coordinates/Realization/SourceColumns.lean`:

```lean
theorem N04RealizationSourceColumns : N04RealizationSourceColumnObligation
```

Given the interface (geometry atoms, pulled height, pulled coefficients and columns) and the
reference jets of the same atlas, prove on all pieces the current jets of the atoms
`sourceFactor`, `sourceFactorInverse`, `leftColumn` and `nuColumn`. Since
`canonicalSource S K z m f y = h x * f x / |planeJacobian (K.chart z m) x|` with
`x = K.inverseChart z m y`, these atoms are products and quotients of interface families.

Definitions and rules: `docs/tasks/N04Realization-Common.md`.

Existing pieces: `N04RealizationPositivePulledHeight`, `N04RealizationCanonicalSourceProduct`,
`N04RealizationFullWeightProductOneHigh`, `N04RealizationDifferenceValue`.
Estimated size: 2,000–4,000 lines.

## Completion standard

See `docs/tasks/N04Realization-Common.md`.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1252–1265 and 1654–1677.
