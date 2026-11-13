# N04Realization-NegativeGeometry

## Problem

Prove `ContinuousFlexibility.Blueprint.N04RealizationNegativeGeometry` in
`src/ContinuousFlexibility/Blueprint/N04Coordinates/Realization/NegativeGeometry.lean`:

```lean
theorem N04RealizationNegativeGeometry : N04RealizationNegativeGeometryObligation
```

For every admissible gauge record, prove on negative pieces (the original typed atlas pieces) the
current jets of the eight geometry atoms and of the pulled height, on a smaller neighborhood chosen
before the auxiliary column. The flow estimate `Blueprint.N04CoordinatesFlowJets : N04FlowJetsTarget`
is proved and may be used.

Definitions and rules: `docs/tasks/N04Realization-Common.md`.

Existing pieces: `N04RealizationRootBoundaryDirections` (current root point towers),
`N04RealizationCanonicalBoundaryInverseJets`, `N04bMatchedRootCollars` (per state),
`N01ControlledLeftRootBoundaryJets`; drafts `N04ActualTravelStripTower`, `N04TravelCircleUniformBounds`,
`N04ActualTravelMixedTowers`, `N04CorrectedFlowInverseCircle`. Missing: root-uniform collar towers of
the chart, the inverse chart, the height and the Jacobian, and the conversion of circle-grading
bounds to the pointwise cost. Estimated size: 10,000–15,000 lines.

## Completion standard

See `docs/tasks/N04Realization-Common.md`.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1545–1678 (Lemma
`uniform-characteristic-flow-constants`; Steps 1–2 of Lemma `current-geometric-jets`).
