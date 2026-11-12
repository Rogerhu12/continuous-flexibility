# R10a-Poisson

## Problem

Construct the terminal Poisson columns and measured flux matrix from the actual
regional inverses, stand-ins, and cutoffs on one reference. Prove
`ContinuousFlexibility.Blueprint.R10aPoisson` in
`src/ContinuousFlexibility/Blueprint/R10a/Poisson.lean` with its stated signature.

The input `Radial.TerminalRegionalData` records the actual weak inverse graphs,
physical cutoff functions, source norms, energy integrals, and numerical budget.
It contains no inner Poisson columns or conclusion about their flux matrix.
Construct the Hilbert columns, subtract the actual Dirichlet correction, retain
all representatives and boundary traces, and prove every `MatchedPieces` clause.

## Completion standard

- The theorem has its stated signature and no `sorry` dependency; its axiom
  report contains only `propext`, `Classical.choice`, and `Quot.sound`.
- All modules used by the proof compile and CI is green.
- The reference, cuts, scalar border, and inverse operators must be those of the
  same input datum. An abstract matrix estimate without actual weak solutions
  and measured boundary fluxes does not complete the task.

## Source

`paper/flexible-surface-readable/06-global-reference-inverse.tex`, lines 661–776.
