# N04Realization-Principal

## Problem

Prove `ContinuousFlexibility.Blueprint.N04RealizationPrincipal` in
`src/ContinuousFlexibility/Blueprint/N04Coordinates/Realization/Principal.lean`:

```lean
theorem N04RealizationPrincipal : N04RealizationPrincipalObligation
```

Given the interface and the reference jets of the same atlas, prove on all pieces the current jets
of `principalA`, `principalAInverse`, `principalB`, `principalC`, `potential`, `dividedA`, `dividedB`
and `dividedC`. On positive pieces the coefficients are `inverseChartPrincipalCoefficients` and the
potential is `inverseChartPotential` (`CoordinateOperatorConstruction.lean`); the divided
coefficients come from the cubic division of the principal difference. On negative pieces the
divided atoms vanish.

Definitions and rules: `docs/tasks/N04Realization-Common.md`.

Existing pieces: `N04RealizationPositiveGaugePotentialBounds`, `N04RealizationPotentialValueBound`,
`N04RealizationActualPositiveGaugeFields`, `N04RealizationPotentialIdentity`,
`N04RealizationCubicOneHighBounds`, `N04RealizationPrincipalHalfBounds`; drafts
`RadialGaugePrincipalTransformation`, `ActualReferenceGaugeCubicDifference`,
`CanonicalWholePositiveAmbientCubicDifference`, `WholeReferenceGaugeDividedRepresentative`,
`RadialGaugePrincipalDifferenceExtension`. Missing: a tower for `coordinatePrincipalDensity` on both
piece types and the negative potential chain. Estimated size: 5,000–9,000 lines.

## Completion standard

See `docs/tasks/N04Realization-Common.md`.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1252–1308 and 1689–1698 (Step 4:
division by the cube).
