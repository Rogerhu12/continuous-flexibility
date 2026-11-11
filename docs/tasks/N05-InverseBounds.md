# N05-InverseBounds

## Problem

Prove `ContinuousFlexibility.Blueprint.N05InverseBounds` in
`src/ContinuousFlexibility/Blueprint/N05/InverseBounds.lean`.

For the controlled reference coordinates and actual volume model, construct
one global inverse and its continuous restriction to the base angular order
two. Record the actual physical reference inverse at the chosen weak exponent.
Prove `N05ReferenceInverseBounds`: the outputs satisfy the literal physical
relation, the same inverse has a fixed material loss at all three endpoint
exponents and every real material and finite angular order, and its first
canonical radial weak derivative has the stated one-angular-derivative bound.

## Completion standard

- The exact theorem and all dependencies compile in CI.
- The axiom audit contains only `propext`, `Classical.choice` and `Quot.sound`.
- No target Schur bound, angular regularity, density, physical realization or
  fixed-loss estimate may be supplied as an extra assumption.
- Constants and loss must have the order of quantifiers in the specification.

## Source

`paper/flexible-surface-readable/08-stable-inverse.tex` lines 75--233.
