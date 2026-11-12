# N05-ReferenceGeometry

## Problem

Prove `ContinuousFlexibility.Blueprint.N05ReferenceGeometry` in
`src/ContinuousFlexibility/Blueprint/N05/ReferenceGeometry.lean`.

Starting only from `N04Statement`, select a construction retaining the entire
`NonlinearPropertiesThrough04` and satisfying
`N05ControlledReferenceCoordinates`. This predicate spells out actual radial
reference charts and heights, comparison with physical cell indices,
coefficient-sized multiplicity, and bounds for the height, its reciprocal and
first derivative, and the radial chart derivative and its reciprocal.

The construction is existential. These properties must be proved for a selected
construction; they must not be inserted into the hypothesis of the frozen N05
statement or assumed for an arbitrary N04 witness.

## Completion standard

- The exact theorem is proved, including preservation of all earlier properties.
- Its proof dependencies compile in CI, with only `propext`, `Classical.choice`
  and `Quot.sound` in its axiom audit.
- Actual coordinate, height, cell and coefficient bounds are required. An
  abstract inverse estimate or assumed coordinate realization does not finish it.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 462--715,
and `paper/flexible-surface-readable/08-stable-inverse.tex` lines 34--167.
