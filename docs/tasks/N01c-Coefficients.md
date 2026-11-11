# N01c-Coefficients

## Problem

Prove `ContinuousFlexibility.Blueprint.N01cCoefficients` in
`src/ContinuousFlexibility/Blueprint/N01c/Coefficients.lean`:

```lean
theorem N01cCoefficients (hN01b : N01bStatement) : N01CoefficientStatement
```

The output retains actual reference, material, spaces and control data on one
common positive-radius neighbourhood, and adds `CoefficientFamilyTameBounds`.
The constants must be uniform in the component and state. Reconstruct data if
needed: the input does not identify every control component with `C.cell m`.

## Completion standard

- The displayed theorem has the same statement and uses only `propext`,
  `Classical.choice`, `Quot.sound`.
- Every proof module is in the root import and CI is green.
- Prove the actual coefficient and mixed-derivative families, with the stated
  weights and one-high-factor bound. A local unweighted smoothness statement or
  a state-dependent existential constant does not suffice.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 761–806,
1303–1539, and the coefficient estimates invoked by Step 1 of
`uniform-characteristic-flow-constants`.
