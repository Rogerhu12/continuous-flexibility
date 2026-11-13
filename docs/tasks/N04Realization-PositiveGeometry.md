# N04Realization-PositiveGeometry

## Problem

Prove `ContinuousFlexibility.Blueprint.N04RealizationPositiveGeometry` in
`src/ContinuousFlexibility/Blueprint/N04Coordinates/Realization/PositiveGeometry.lean`:

```lean
theorem N04RealizationPositiveGeometry : N04RealizationPositiveGeometryObligation
```

For the retained start, its choices, the reference family `Y, H` and any piece enumeration and
normalization buffer, choose one positive transport family `τ, σ, Q` with its transport matching
on a smaller state neighborhood and the identity at the reference state. Prove, on positive pieces,
the current jets of the eight geometry atoms (chart, inverse chart, height, Jacobian and their
inverses) and of the pulled height. On positive pieces the chart is `Y ∘ σ`
(`wholePositiveReferenceGaugeChart`), the inverse chart is `τ ∘ Y⁻¹`, and the height is
`H(σ ·)/Q(σ ·)`. The controls of the family must have costs bounded by a power of the sampled `E0`,
uniformly in the component; the existing selection
`n04Coordinates_exists_fixed_positive_family(_with_log_bounds)` does not give that.

Definitions and rules: `docs/tasks/N04Realization-Common.md`.

Existing pieces (none has a caller yet): `N04RealizationOneSidedTransportDirections` (joint tower of
`τ` from raw endpoint towers), `N04RealizationFixedRadialPullback`, `TameInverseJets`
(`inverseFamilySmoothDirections`), `TameInverseFixedBaseBounds`, `N04RealizationPositiveAngularInverse`,
`N04RealizationEnvelopeJacobian`, `N04RealizationActualPositiveHeightBounds` (`Q`, `1/Q`),
`N04RealizationPositiveGaugeHeightBounds`, `N04RealizationPositivePulledHeight`; drafts
`WholePositiveTransportPolynomialAssembly`, `WholePositiveCollarPolynomialEnvelope`,
`OneSidedLogAngularJets`. Missing: the raw endpoint towers, a tower and bounds for `σ`, and the
uniform `E0` costs of the controls. Estimated size: 6,000–9,000 lines.

## Completion standard

See `docs/tasks/N04Realization-Common.md`.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1218–1250 (coordinates on a positive
component) and 1679–1687 (Step 3 of Lemma `current-geometric-jets`).
