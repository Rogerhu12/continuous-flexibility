# N04b-CanonicalConstruction

## Problem

Construct the actual canonical atlas of a corrected field satisfying the
cumulative N01--N03 properties and `N04bFieldRegularity`, including the
explicit correction's radial optical flow at the reference state.

Prove `ContinuousFlexibility.Blueprint.N04bCanonicalConstruction` in
`src/ContinuousFlexibility/Blueprint/N04b/CanonicalConstruction.lean`.
The theorem takes the explicit cumulative data and their material,
physical-space, N01--N03 and raw-field hypotheses. Its conclusion is

```lean
∃ K : CanonicalData S,
  N04PartA A.val S C K base ε ∧ N04PartB S C L K base ε
```

Construct travel coordinates from the actual corrected characteristic
flows, split each negative component at the actual travel level
`σ = T/2`, regularize the root coordinates, and choose the actual density
height gauge. Keep the canonical intervals and their common radius
independent of the state. The physical negative halves may move. Derive their reference radial
metadata from the actual optical half-travel cut; the arithmetic midpoint
is not used as a travel identity.

Prove the current planar partition, the actual smooth closed inverse
identities, normalization, periodicity and reflection identities, the
operator formula, the negative coefficients `(1,0,-ξ)`, the stated cut
transmission equation, and the positive interior divided differences.
The exact height, source and operator definitions must remain the actual
pullback formulas.

## Completion standard

- The theorem has exactly its displayed source statement, contains no
  `sorry`, and its transitive axiom audit contains only `propext`,
  `Classical.choice`, `Quot.sound`.
- The input has no canonical chart, density, normal-form or transmission
  hypothesis. All such objects and identities are constructed.
- Boundary values and derivatives use the actual smooth inverse extension;
  arbitrary totalized inverse values are not a boundary construction.
- All modules compile and full CI is green after merging current main.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex`, lines 992--1303.
