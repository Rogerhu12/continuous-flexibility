# N05-GraphIdentification

## Problem

Prove `ContinuousFlexibility.Blueprint.N05GraphIdentification` in
`src/ContinuousFlexibility/Blueprint/N05/GraphIdentification.lean`.

Identify the literal `ReferenceCanonicalRelation` with the independently
constructed inverse. Recover the physical source from its actual canonical
representatives, identify the auxiliary scalar through source compatibility,
use physical graph uniqueness, and identify the left constant from the actual
canonical endpoint class. The resulting equality includes all canonical L²
coordinates and all three scalar components.

## Completion standard

- The exact theorem and all dependencies compile in CI.
- The axiom audit contains only `propext`, `Classical.choice` and `Quot.sound`.
- The physical relation is unchanged. Defining it as the inverse range, assuming
  uniqueness, or proving uniqueness only on a smooth core is insufficient.

## Source

`paper/flexible-surface-readable/08-stable-inverse.tex` lines 234--256.
