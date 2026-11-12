# N04Coordinates-Realization

## Problem

Prove `ContinuousFlexibility.Blueprint.N04CoordinatesRealization` in
`src/ContinuousFlexibility/Blueprint/N04Coordinates/Realization.lean`:

```lean
theorem N04CoordinatesRealization
    (hFlowJets : N04FlowJetsTarget) (hN04b : N04bStatement) : N04cStatement
```

The flow-tool input is the independent raw-field ODE theorem in
`src/ContinuousFlexibility/Analysis/N04FlowJetsTarget.lean`.
Construct a legitimately controlled correction and canonical-coordinate
witness, while retaining the cumulative N01–N03 conditions, and derive
the exact all-order potential and divided-coefficient bound on one
common state neighborhood with one fixed loss.

The same witness must also carry both `CanonicalPrimitiveGeometry` and
`CanonicalGeometry.PrimitiveGeometryProperties` from the current parent
statement. The latter retains the actual radial reference gauge, reference
principal positivity and unit-piece jets, current-minus-reference spatial
jets and their `SmoothDirections` tower with the prescribed height gain,
the radial supported auxiliary source, and `TransmissionGeometry`.
In particular, relative transport matching alone does not replace the
actual forward chart and height first-jet matching at roots and at the
state-dependent middle cuts. See `docs/notes/N07a-interface-repair.md`.

The proof includes the actual root charts and heights, global negative
pieces and cut matching, positive reference interpolation and finite
boundary jets, inverse coordinates, ordinary boundary jets, and the
actual three vanishing numerator jets at both ends. Quantitative
constants must have the exact quantifier order in N04Properties.
The source-pairing identity is already available from N04PartA.

An arbitrary PartA/B witness is not assumed to have the required bounds.
If a witness is replaced or its neighborhood shrunk, every retained
N01–N03 and canonical clause must be proved for that same replacement.
Per-state or per-component positive collars do not by themselves give
the required common state neighborhood. No final canonical estimate may
be inserted as a new hypothesis.

## Completion standard

- The theorem has exactly the statement above and contains no `sorry`.
- Its axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
- Every used module compiles and the complete CI is green.
- The exact parent `N04Coordinates` must assemble this theorem and
  `N04CoordinatesFlowJets` without a local `sorry`; it is complete only
  after both dependencies also have the permitted axiom set.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex`, the root-coordinate
and positive-crossing constructions and lines 1211–1760 for reference
interpolation, quantitative geometry, general-state bounds and source
conversion. Existing coordinate, Seeley, cubic-division, source-measure,
and state-neighborhood modules should be reused.
