# R10a-Regional

## Problem

Prove `ContinuousFlexibility.Blueprint.R10aRegional` in
`src/ContinuousFlexibility/Blueprint/R10a/Regional.lean` with its stated signature.

From `R06Statement`, `R09Statement`, and the parameterized `R10aGeometrySupply`,
choose one reference and construct `Radial.TerminalRegionalData` for every even
frequency. The record requires the actual bounded inner Dirichlet and outer
Robin inverse operators, their two-sided weak graph identities and retained
representatives, the selected unit boundary states and margin, and actual
physical stand-ins and cutoffs with their source, energy, and error budgets.

The inner border is the fixed metric-variation column of that reference. The
outer inverse uses the radial Hilbert measure. The first-band length must be
chosen with an inner inverse bound uniform in that length; later-band budgets
use the preceding cell's attenuation. Preserve the quantifier order that fixes
the selected sequence and first-band margin before extending the first cones.
The tool tasks `Tool-R10a-Inner` and `Tool-R10a-Outer` provide analytic components;
their operators still have to be identified with the frozen physical graphs.

## Completion standard

- The theorem has its stated signature, with no `sorry` dependency. Its axiom
  report contains only `propext`, `Classical.choice`, and `Quot.sound`.
- All modules used by the proof compile and CI is green.
- Every clause of `TerminalRegionalData` is proved for the same reference and
  matching cuts. Conditional operator or residual estimates do not close this
  construction; derive their hypotheses from the actual supplied geometry.
- Do not replace the fixed central column or weaken the weak test, support,
  scalar-row, endpoint trace, or uniqueness clauses.

## Source

`paper/flexible-surface-readable/06-global-reference-inverse.tex`, lines 352–776.
