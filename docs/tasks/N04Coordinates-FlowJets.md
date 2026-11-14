# N04Coordinates-FlowJets

## Problem

Prove `ContinuousFlexibility.Blueprint.N04CoordinatesFlowJets` in
`src/ContinuousFlexibility/Blueprint/N04Coordinates/FlowJets.lean`:

```lean
theorem N04CoordinatesFlowJets : N04FlowJetsTarget
```

The exact target is defined in
`src/ContinuousFlexibility/Analysis/N04FlowJetsTarget.lean`.
It quantifies actual spatial Frechet jets of the raw periodic scalar field
in two independent parameters and the angle, on a fixed parameter box and
closed time interval. From the actual ODE and those raw bounds, prove
joint spatial smoothness, angular equivariance, the exponential angular
Jacobian bounds, and fixed-loss mixed-jet bounds for the actual flow
displacement.

The low state order and loss precede every derivative order. Output
constants precede the state, material envelope, field and chosen solution.
The angular integral majorant alone controls the Gronwall exponent;
possibly large external-parameter derivatives enter through material
powers. A supplied derivative tower or an assumed flow-jet estimate does
not complete this task.

## Completion standard

- The theorem has exactly the statement above and contains no `sorry`.
- Its axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
- Every used module compiles and the complete CI is green.
- A finite-order, angular-only, relative, or conditional replacement is
  not the target.

This is a subnode of N04Coordinates. The parent implication is assembled
without changing N04bStatement or N04cStatement; the parent remains open
until both subnodes pass their complete axiom audits.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1531–1703,
the general-state flow lemma and Step 1 / Step 5 of the geometric-jet lemma.
Reuse the actual scalar-flow and Tool-OneHighFactor modules already in
the repository and the state interpolation/product closure.
