# N01c-Flows

## Problem

Prove `ContinuousFlexibility.Blueprint.N01cFlows` in
`src/ContinuousFlexibility/Blueprint/N01c/Flows.lean`:

```lean
theorem N01cFlows (hSpeeds : N01SpeedStatement) : N01Statement
```

Derive `OrdinaryFlowFamilyTameBounds` for the actual ODE solutions from the
quantitative speed stage, retain the coefficient bounds on the same common
neighbourhood, and assemble the exact N01 properties.

## Completion standard

- The displayed theorem has the same statement and uses only `propext`,
  `Classical.choice`, `Quot.sound`.
- Every proof module compiles in CI (the root import is generated), and CI is green.
- Prove the complete directional towers and the uniform one-high-factor
  estimates with the actual component weights and radial endpoint factors.
- Keep one common base and positive radius. Only the additional parameter loss
  and constants may depend on the parameter order. A generic local
  `SmoothTameOn` statement alone does not meet these quantifiers.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex`, `circle-flow`, lines
1536–1613 (`uniform-characteristic-flow-constants`) and lines 1615–1725
(`current-geometric-jets`, especially Steps 1 and 5).
