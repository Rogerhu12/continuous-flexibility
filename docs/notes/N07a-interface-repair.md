# Canonical geometry and weak-period interface repair

## Scope

This change follows the audit in N07a, branch `line/N07a`, PR #37. It preserves
the exact public theorem signatures of N02N03, N04Coordinates, N04, N05, N06,
and N07a. It strengthens the construction-stage propositions carried through N03 and N04
and repairs the actual weak physical representation in N06. This document records
the interface audit made while N07a was open. The analytic conclusions are proved
separately by N07aAngular, N07aLinear, N07aSmooth, and their N07a assembly.

## Full-period physical tests

The old `PerturbedCanonicalRelation` quantified over `RadialTest D φ`, whose
angular period is `2 * Real.pi`, but all four physical pairings used
`angularMean`, the half-period mean. The reference distributional graph
uses `radialAngularMean`, the full-period mean. A general allowed test need
not have matching values or derivatives at the half-period endpoints, so
the intended integration-by-parts identity does not follow with the old
pairing. The relation now uses `radialAngularMean` in exactly those four
places. Canonical L² spaces and canonical tests retain period π.

The old witness clause was exactly:

```lean
HasCanonicalRepresentation D S C K z U F η f ∧ referenceRow D η = 0 ∧
```

`HasCanonicalRepresentation` identifies classes on one canonical period;
by itself it does not assert global periodicity of the chosen physical
functions. The relation now retains the actual π-periodicity of both
physical witnesses before its normalization and weak-equation clauses:

```lean
HasCanonicalRepresentation D S C K z U F η f ∧
Function.Periodic η (0, Real.pi) ∧ Function.Periodic f (0, Real.pi) ∧
referenceRow D η = 0 ∧
```

This is the period of the physical source and unknown in the construction.
It is already retained at the reference stage by `OutputRealization` and
`SourceMember`. No classical smoothness, inverse bound, or weak change of
variables is added as a witness premise.

## Primitive geometry carried by the coordinate construction

The previous terminal clause of `NonlinearPropertiesThrough04` was exactly:

```lean
N04Properties D T S C L K base loss ε
```

N04's qualitative chart identities and reflection/period equivariance do
not themselves fix the reference angular gauge. Its coefficient-jet clause
bounds only the potential and positive-piece divided differences by
`B * E0^B * (1 + stateGrading + |q|)`. It does not retain the genuine
current-minus-reference height gain or the spatial and parameter jets of
the actual coordinate, height, Jacobian, and source factors. The final
smooth pairing identity is not a quantitative comparison of gradings.
Also, the original normalization region is only required to contain the
reference-column support; the actual auxiliary source was not required
to be radial or supported in that frozen region.

The terminal coordinate payload is now:

```lean
N04Properties D T S C L K base loss ε ∧
CanonicalGeometry.PrimitiveGeometryProperties D T S C L K base ε
```

`N04cStatement` carries the identical payload for the same existentially
chosen objects, and `N04_of_nodes` explicitly preserves it when assembling
N04. The primitive definitions were moved, with their public names
unchanged, from `Statements/N07aCanonicalGeometry.lean` into
`Statements/Nonlinear.lean`; the former module is a compatibility import.

The payload concerns only actual geometric functions:

- The reference chart and inverse preserve the angle, and the height is
  radial.
- The reference leading coefficient is positive; on positive pieces the
  angular coefficient has the prescribed linear endpoint degeneracy.
- Spatial jets of the actual unit-rescaled charts, inverse charts, height,
  Jacobian, source factor, principal coefficients, potential, divided
  differences, scalar columns, lengths, and material ratios obey reference
  coefficient bounds.
- The actual current-minus-reference jets have the height factor
  `H^(3/4)`, a fixed derivative loss, and a genuine directional-derivative
  tower with one high factor for each parameter order.
- The actual compatibility source is radial and supported in the frozen
  normalization region.
- Actual forward chart and height first jets retain the fixed root and
  middle-cut transmission identifications described below.

The coordinate construction must prove these facts. The payload assumes
no inverse, commutator, Fourier realization, solution regularity, weak
change of variables, local finiteness, solution trace matching, or grading
equivalence. Those are analytic conclusions proved by N07a in separate modules.
In particular, the N07a band-preservation and bounded-coefficient lemmas consume
these named primitive facts explicitly; they do not manufacture them from
the former qualitative clauses.

## Manuscript correspondence

### Spatial regularity of the actual return correction

The previous last clause of `N03Properties` was exactly:

```lean
SmoothTameOn
  (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
    (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
  S.sourceGrading ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
  (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
    L.error (liftSectorParameter S C z.1.1) z.1.2 z.2)
```

This is the smooth-tame assertion for `L.error`. The other clauses fixed the leading coefficient, germs at
roots and on positive pieces, reflection, characteristic returns, and the
action of the corrected divergence on actual `HeightPair` fields. They did
not retain open-annulus smoothness and π-periodicity of the actual corrected
`b` and `c` functions. Qualitative N04 conjugation on the open pieces does
not itself provide a proved function-level recovery of those coefficients
across the artificial cuts; Lean's totalized `fderiv` cannot be treated as
an implicit differentiability hypothesis.

The final N03 payload now conjoins
`ReturnCorrectionSpatialProperties D S C L base ε`. It asserts exactly
`ContDiffOn ℝ ∞` of these two actual coefficients on `annularOpen D` and
their π-shift identity on that open set. There is no endpoint extension,
inverse bound, solution regularity, trace, or matching-jet premise. The
leading coefficient remains fixed to the original one and its smoothness
and positivity are proved separately from N01.

These are raw outputs of the corrected-speed formula and
`b̂ = a d̂`, `ĉ = a (d̂² − v̂²)` in
`paper/flexible-surface-readable/07-fixed-geometry.tex`, lines 930–953.
The correction is supported strictly inside each negative component
(lines 974–976), so those formulas are smooth through the artificial cut
and retain the original germs at its component endpoints. N02N03 must
prove this added construction obligation. The assembly continues to carry
the same cumulative N03 construction into N04–N06, and neighborhood
restriction explicitly preserves the new clause. This records an absent
primitive output used by the intended proof, not a proof that the former
existential N07a proposition was false.

The geometric obligations are the actual uniform physical geometry,
regularized reference charts, geometric weight conversion, and current
geometric jets in `paper/flexible-surface-readable/07-fixed-geometry.tex`.
The radial compatibility source and its frozen support are chosen in
`paper/flexible-surface-readable/08-stable-inverse.tex`. The need for the
original source in the normal recurrence, the one-high-factor bound, and
the fixed total loss is explicit in that file's lines 658–774.

## Primitive first jets of the fixed transmission geometry

The qualitative `PhysicalTransmissionTarget` takes value/conormal matching as
inputs. It therefore does not supply the matching data for the actual current
and reference coordinate constructions. N04's open-piece identities and raw jet
bounds did not retain the root interface first jets needed to place an arbitrary
smooth physical candidate in the same N05 reference graph. Also, the existing
middle-cut clause evaluates `canonicalHeight` through `inverseChart` at a
boundary, while the inverse identities constrain that candidate only in the open
canonical strip. Such a totalized endpoint value is not automatically the trace
of the actual interior inverse.

`CanonicalGeometry.TransmissionGeometry` now retains three raw construction
outputs. It classifies adjacent physical interfaces as roots or the designated
middle cuts; gives equality of the actual forward chart and height values and
first derivatives at roots after fixed normal endpoint orientations are aligned;
and gives the actual forward chart/height first-jet identity at middle cuts.
The latter height identity gives exactly the existing Robin relation
`Wr' = -Wl' - W/(2*cutRadius)`. The same fixed endpoint identifications cover the
reference construction and every admissible current state. The candidate
`inverseChart` is not assigned new boundary values; actual traces are recovered
from the smooth nonsingular forward chart by its local inverse.

These are the coordinate/height facts explicitly used in
`paper/flexible-surface-readable/07-fixed-geometry.tex`, lines 1733–1760.
The construction stage must prove them, and neighborhood restriction preserves
them on the same objects. They do not assert membership of a solution in the
reference graph, any inverse estimate, or higher regularity of a solution. N07a
proves reference-graph membership of arbitrary physical candidates, weak gluing,
and uniqueness from these geometric facts. It constructs the candidate's graph
and volume realizations before applying the N05 graph equivalence and N06
injectivity. This records the exact missing primitive output needed by that
proof; it does not claim a counterexample to the former complete existential
N07a statement.

## Construction obligations and the analytic proof

The N02N03 proof must construct the actual corrected coefficients' spatial
regularity and periods. The N04Coordinates proof must construct the primitive
geometry payload. The N06 proof must retain the actual physical witness periods
and prove the full-period distributional identity. These upstream construction
obligations remain explicit in their task files and cumulative statements.

The N07a proof derives the actual relative-operator bounds, smooth physical
reconstruction, fixed-loss tame estimates, conservation cancellation, and the
smooth-tame inverse. Its Linear subnode constructs domain membership for every
original normalized HeightPair and proves uniqueness against every such candidate.
The same base source, N05 domain, N06 inverse, physical decoder, and final inverse
family are retained. No inverse regularity, source membership, candidate-domain
membership, solution trace, or tame estimate is added as a construction premise.
The original exact N07a theorem is assembled from these analytic subnodes.
