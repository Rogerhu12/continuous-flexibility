# Canonical geometry and weak-period interface repair

## Scope

This change follows the audit in N07a, branch `line/N07a`, PR #37. It preserves
the exact public theorem signatures of N04Coordinates, N04, N05, N06, and
N07a. It strengthens the construction-stage proposition carried through N04
and repairs the actual weak physical representation in N06. N07a remains
open; these interface changes do not prove its analytic estimates.

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

The coordinate construction must prove these facts. The payload assumes
no inverse, commutator, Fourier realization, solution regularity, weak
change of variables, local finiteness, trace matching, or grading
equivalence. Those remain analytic conclusions to prove. In particular,
the existing N07a band-preservation and bounded-coefficient lemmas consume
these named primitive facts explicitly; they do not manufacture them from
the former qualitative clauses.

## Manuscript correspondence

The geometric obligations are the actual uniform physical geometry,
regularized reference charts, geometric weight conversion, and current
geometric jets in `paper/flexible-surface-readable/07-fixed-geometry.tex`.
The radial compatibility source and its frozen support are chosen in
`paper/flexible-surface-readable/08-stable-inverse.tex`. The need for the
original source in the normal recurrence, the one-high-factor bound, and
the fixed total loss is explicit in that file's lines 658–774.

## Remaining obligations

The N04Coordinates proof must construct the new primitive payload. The
N06 proof must retain the actual physical witness periods and prove the
full-period distributional identity. N07a must still derive the actual
relative-operator bounds, smooth physical reconstruction, fixed-loss tame
estimates, conservation cancellation, and the genuine smooth-tame inverse.
The repair does not bypass any of these requirements.
