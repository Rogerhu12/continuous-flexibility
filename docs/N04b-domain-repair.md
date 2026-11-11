# N04b: repaired physical domain contract

## Scope and status

The implementation at `aa44e9dbc540fe414ec7898edf9c5f27bdcf293d`
adds `CanonicalData.physicalDomain z m` for current physical pieces.
Canonical intervals and cut radii remain state independent.
The existing `physicalLeft` and `physicalRight` fields now describe
reference geometry through `referencePhysicalPieceOpen`; they do not
define the current domain.

Reference domains remain radial strips. Positive domains stay equal to
their reference strips on admissible states. Negative current domains
may have curved boundaries.

The statement layer, Blueprint Part A/B, Assembly, and the integrated N04a
reference-atlas proof use the same repaired contract. This change does not
prove N04b or its actual characteristic construction. The
[fixed-cut audit](N04b-fixed-cut-audit.md) remains a mathematical obstruction
under investigation, not a Lean refutation of the former existential
statement.

## Exact clauses being repaired

The former domain definition was

```lean
physicalPieceOpen S K m :=
  Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ univ
```

and the cut-pair clause included

```lean
K.physicalRight (K.cutPair n).1 =
  K.physicalLeft (K.cutPair n).2
```

Together these required a state-independent physical radial cut. The
manuscript instead cuts at `σ = T / 2` in the actual corrected travel
coordinates. Its physical location can depend on the state and angle.
See `paper/flexible-surface-readable/07-fixed-geometry.tex`,
lines 995–1027 and 1178–1189.

The old endpoint equality is retained in `CanonicalReferenceCutPairs`
with its reference-only meaning. Current geometry is supplied separately
by `CanonicalCurrentCutPair`.

A set-valued domain avoids an additional physical radial-graph assumption.
The characteristic identities are

\[
 \sigma_r=v\varphi_\theta-d\sigma_\theta,\qquad
 \varphi_r=v\sigma_\theta-d\varphi_\theta,\qquad
 J=v(\varphi_\theta^2-\sigma_\theta^2)>0.
\]

They imply radial monotonicity with the travel angle `φ` held fixed.
They alone do not imply `σ_r > 0` with the physical angle held fixed:
the local derivative matrix with rows `(-1,1)` and `(-3,2)` satisfies
these identities for `v = 1/3`, `d = 5/3`, with positive
`U_θ = 1`, `V_θ = 3`. This demonstrates a missing local implication;
it is not a complete counterexample to N04b.

## Shared geometry and actual boundary inverses

`CanonicalGeometry` is the shared geometric predicate used by
`N04PartA` and `N04Properties`. It retains the radial reference
bounds, signs, and null partition and adds:

- Equality of the reference current domain with
  `referencePhysicalPieceOpen`.
- Open, nonempty current domains inside the annulus, with the appropriate
  sign, angular-periodicity, and reflection properties.
- Equality of positive current domains with their reference strips.
- A planar null exceptional set for the unique current partition at
  every admissible state.
- The existing interior chart, inverse, height, Jacobian, and symmetry
  identities on the actual current domains.
- Domain agreement inside the normalization region, together with the
  existing equality of charts and heights with their reference values.
- Actual closed maps-to properties, both closed inverse identities, and
  smooth nondegenerate forward charts with positive smooth heights on
  `physicalPieceClosed = closure physicalPieceOpen`.

The canonical closed strip is
`Icc (K.left m) (K.right m) ×ˢ univ`.
At every physical frontier point, `CanonicalBoundaryInverseGerm F G p`
requires an `OpenPartialHomeomorph` whose forward function is `F`,
whose source contains `p`, and whose inverse is smooth at `F p`.
The stored inverse `G` must agree with that true inverse on a full
neighborhood of `F p`.

This fixes the boundary values and ordinary derivatives used in
transmission. Interior inverse identities alone did not constrain those
stored boundary jets. The full germ condition, combined with the closed
inverse identities, also gives smoothness of the stored inverse at every
canonical boundary point.

The existing projection API includes:

```lean
hA.referenceBounds m
hA.referenceDomain m
hA.domains z hz hsector m
hA.partition z hz hsector
hA.charts z hz hsector m
hA.boundary z hz hsector m
hA.normalization z hz hsector m
```

## Current cut geometry and preserved formulas

The physical cut is derived from the actual left inverse:

```lean
canonicalCutPoint S K z n θ :=
  K.inverseChart z (K.cutPair n).1 (K.cutRadius n, θ)
```

`CanonicalCurrentCutPair` requires:

- The right inverse at the common canonical radius has the same trace.
- The whole cut lies inside the original negative component.
- The two current domains are disjoint and their union is exactly that
  component with the cut removed.
- The two inverse images of the entire canonical zero-radius line are
  exactly the original left and right root circles.

`CanonicalCutGeometry` combines reference metadata with these current
conditions. `CanonicalCutOperatorProperties`, shared by `N04PartB`
and `N04Properties`, combines that geometry with the unchanged
transmission and actual operator identities.

The definitions of `canonicalHeight`, `canonicalSource`, and
`canonicalOperator` are unchanged. The following conclusions and
quantifiers also remain:

- Transmission for every smooth physical test:
  `Wr = Wl` and `∂ξ Wr = -∂ξ Wl - Wl / (2 * R)`.
- The actual conjugated operator identity for every smooth canonical test.
- Negative principal coefficients `(1,0,-ξ)`.
- The positive cubic-difference identity on the canonical open interval.
- The same uniform potential/divided-coefficient jet estimate, including
  its neighborhood, derivative loss, material factors, and state quantifiers.
- The actual source pairing, whose physical integral now uses
  `physicalPieceOpen S K z m`.

`N04Properties` is the conjunction of the shared geometry, shared
cut/operator predicate, original jet estimate, and
`CanonicalSourcePairing`. `Assembly.lean` unpacks and reassembles
these four properties on the same data. Its unconditional theorem receives
no additional hypothesis.

## Reused construction and reference lemmas

`N04bMovingDomains` defines actual preimages of travel subintervals.
Its theorems prove openness, restricted bijections, the two-half split,
and identification of the middle cut with the inverse on the full
travel strip. The inverse is evaluated at an interior travel level.

`N04bCutCurve` proves that this actual smooth inverse slice has planar
measure zero, and that countably many such cut curves remain null.
It does not require a radial graph for a cut.

`N04bAtlasBoundary` uses the existing forward and inverse affine
formulas to construct a genuine global homeomorphism. It supplies the
closed maps, boundary inverse germs, and planar partition obtained from
the countable reference radial exception.

The integrated `N04CanonicalAtlas` uses these lemmas and sets its
current domain equal to its fixed reference strip for every state.
Its chart, inverse, and Liouville-height formulas are unchanged.
This proves geometric reference-atlas facts; it does not assert
characteristic normal form or the operator transmission law.

## Remaining analytic obligations

The intended negative constructor must establish, from the actual
corrected flow and its actual inverse,

\[
 \Omega_L=\{0<\sigma<T/2\},\qquad
 \Omega_R=\{T/2<\sigma<T\},\qquad R=(3T/4)^{2/3}.
\]

It must prove the root-smooth charts and heights, genuine boundary
inverse germs, actual negative principal density, and cut transmission.
These are construction conclusions, not assumptions inserted into
Part A or N03.

The next construction split is actual smooth periodic hyperbolic-field
realization preserving Through03, followed by construction of the moving
atlas. The existing N03 interface does not itself state smoothness of
arbitrary stored corrected coefficients; that bridge must be proved or
the actual corrected witness reconstructed.

N04b may retain the fixed affine positive charts and use the actual
positive quotient on the open interval. Smooth boundary division and its
uniform bounds remain obligations of N04Coordinates. Source conversion
must establish the angular fundamental-strip image using the inverse on
the fixed canonical rectangle, rather than assuming physical vertical
segments remain inside a curved current domain.

Compilation and axiom audits remain the acceptance gate. This note does
not label the characteristic construction complete.
