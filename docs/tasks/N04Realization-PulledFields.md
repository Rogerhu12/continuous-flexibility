# N04Realization-PulledFields

## Problem

Prove `ContinuousFlexibility.Blueprint.N04RealizationPulledFields` in
`src/ContinuousFlexibility/Blueprint/N04Coordinates/Realization/PulledFields.lean`:

```lean
theorem N04RealizationPulledFields : N04RealizationPulledFieldObligation
```

Given the geometry interface on all pieces, prove on all pieces the current jets of the three
physical coefficients and of the physical left and `ν` columns, pulled back by the inverse chart.
The physical families are tame in the state by N01–N03 (`NonlinearPropertiesThrough03` of the
start); the work is the composition with the inverse chart.

Definitions and rules: `docs/tasks/N04Realization-Common.md`.

Existing pieces: `N04RealizationPositiveCoefficientPowerBounds`, `N04RealizationPositiveCoefficientJoint`,
`N04RealizationMovingPointHeightBounds`, `N04RealizationColumnPowerBounds`,
`N04RealizationLeftColumnTower`, `N04RealizationNuColumnTower`, `N04RealizationHeightMovingEvaluation`;
draft `N04CoefficientSampleJetTower`. Estimated size: 2,000–4,000 lines.

## Completion standard

See `docs/tasks/N04Realization-Common.md`.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1700–1717 (Step 5 of Lemma
`current-geometric-jets`).
