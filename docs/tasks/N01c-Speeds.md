# N01c-Speeds

## Problem

Prove `ContinuousFlexibility.Blueprint.N01cSpeeds` in
`src/ContinuousFlexibility/Blueprint/N01c/Speeds.lean`:

```lean
theorem N01cSpeeds (hCoefficients : N01CoefficientStatement) : N01SpeedStatement
```

The new predicate `CharacteristicSpeedTameBounds` concerns the actual ordinary
minus-characteristic speed. It includes spatial smoothness, parameter towers,
and weighted estimates at the simple-root endpoints. The preceding coefficient
bounds and all geometric conditions must hold for the same output data.

## Completion standard

- The displayed theorem has the same statement and uses only `propext`,
  `Classical.choice`, `Quot.sound`.
- Every proof module compiles in CI (the root import is generated), and CI is green.
- Establish the actual quantitative type and control-ratio estimates needed to
  differentiate the square root. Totalized square roots and derivatives do not
  supply smoothness. Keep one low-order neighbourhood for all orders.
- The parameter loss may depend on `k`, but is chosen before the spatial order,
  component, point, state and increments. No order-dependent radius is allowed.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1536–1613,
especially Step 1 of `uniform-characteristic-flow-constants`, together with
`quantitative-root-collars` and `quantitative-optical-controls` cited there.
