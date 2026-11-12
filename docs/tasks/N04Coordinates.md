# N04Coordinates

## Problem

The uniform bounds of the potential and of the divided differences, and the conversion of sources (rest of Proposition 7.8).

The same chosen coordinates and neighborhood carry both
`CanonicalGeometry.PrimitiveGeometryProperties` and `CanonicalPrimitiveGeometry`.
The latter is N07b's state-dependent chart, closed-domain, height, Jacobian and
material-sample certificate. The former retains the radial reference gauge,
reference positivity and unit-piece jets, genuine current-minus-reference
spatial/parameter jets, and the radial compatibility source supported in the
frozen normalization region. These are construction-stage facts about the
actual functions, not inverse or commutator estimates. The precise interface
repair and its manuscript sources are recorded in
`docs/notes/N07a-interface-repair.md`.

Prove `ContinuousFlexibility.Blueprint.N04Coordinates` in `src/ContinuousFlexibility/Blueprint/N04Coordinates.lean`:

```lean
theorem N04Coordinates (hN04b : N04bStatement) : N04cStatement
```

The primitive coordinate payload includes `CanonicalGeometry.TransmissionGeometry`:
classify actual adjacent interfaces as roots or designated middle cuts, prove the
actual forward chart/height values and first derivatives match at roots after the
fixed endpoint orientations are aligned, and prove the forward-jet middle-cut
Robin identity at `canonicalCutPoint S K z k θ`. This point is on the actual
state-dependent physical cut; only the canonical cut radius is fixed.
These are construction-stage facts from the transmission domain in §7.
Boundary values of an unconstrained `inverseChart` are not substitutes
for the traces of its actual interior inverse.

## Completion standard

- `theorem N04Coordinates` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.N04Coordinates` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses compiles in CI (the root import is generated) and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1497–1760.
