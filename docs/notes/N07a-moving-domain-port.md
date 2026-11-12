# N07a: migration to the state-dependent N07b atlas

This continuation stays on `line/N07a` (PR #37). It merges main through
`93f5906c14e93f96e5f731719c65c5330c16e9a5`, which integrates N07b and R11a.
The frozen public N07a statement is retained.

## The two primitive certificates

The terminal N04 output retains both certificates, in this order:

```lean
CanonicalGeometry.PrimitiveGeometryProperties D T S C L K base ε ∧
  CanonicalPrimitiveGeometry D T S C L K base ε
```

The first is the certificate already introduced on this branch; the second
is N07b's certificate on main. Restriction and blueprint assembly carry both.
There is one definition of `nuColumnField`.

## Raw first-jet location repair

In `CanonicalGeometry.CutFirstJetMatching`, the old line was exactly:

```lean
let p : PolarPoint := (K.physicalRight i, θ)
```

N07b's general-state negative cut is the inverse image of the canonical cut
radius. Its radial coordinate can depend on the angle and the state, so the
old fixed reference endpoint is not the current interface. The replacement is:

```lean
let p : PolarPoint := canonicalCutPoint S K z k θ
```

This changes the evaluation point in the existing raw geometric matching
predicate. It does not assert any trace, regularity, inverse estimate, or
equation for an unknown solution. No conclusion of N07a is added to its
hypotheses.

## Domain-sensitive proof changes

Reference interval covers, affine unit-coordinate estimates, and reference
transport targets use `referencePhysicalPieceOpen`. Current measure changes,
inverse identities, compact test pullbacks, physical representatives, and
reconstruction estimates use `physicalPieceOpen S K z m`.

The material-ratio and first-forward-derivative certificates are proved from
the original raw reference/current jets after one neighborhood restriction.
Higher inverse-function derivatives retain their total excess-order budget
until a single interpolation estimate is applied. The sampled subpower
envelope is absorbed only after each complete finite expression is formed.

Compact current-piece supports are counted using actual-point material
ratios and the disjoint reference interval lengths. Continuous inequalities
extend through the planar null partition supplied by N07b. Neither argument
identifies a current negative half with its old fixed radial rectangle.

The original `B.Space` reference-graph witness is recovered from the actual
base inverse. It supplies the product-test trace argument for the same
unknown; no trace-matching premise is introduced for a solution.

## Regularity across the actual cut

All canonical weak jets first produce a closed within-Taylor jet tower.
Arbitrary periodic angular tests in the original reference graph determine
the value and first derivative traces. The primitive reference/current
transport carries those traces to the actual cut for the same physical
remainder.

The common local chart is built from the smooth cut curve and a fixed
transverse vector. Its differential at the center is the genuine inverse
chart differential. A finite-order neighborhood controls the side signs,
and the inverse-function theorem applied to this globally smooth tubular
map supplies smooth coordinates on an open neighborhood. In particular,
the proof does not infer a common smooth neighborhood from
`ContDiffAt` of infinite order at a single boundary point.

The normalized canonical equation already stored in the solution data
gives the actual physical divergence equation. A radial quadratic probe
in N04 proves that its transformed normal coefficient is nonzero at the
cut. The same smooth physical coefficients and source then force all
within jets to match. Closed Taylor gluing yields a smooth field across
the curve. The curve is null because the differentiable inverse chart
maps a canonical vertical null line to it; this preserves the physical
a.e. class and all angular L² jets when the two halves are assembled.
Only after this step are the smooth component fields restricted to the
fixed reference halves for the existing angular patching argument.

## Validation record

The first integration CI run is
<https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43161191472>.
The subsequent migration group is being checked against that integration.
Final module counts and the exact axiom output belong in the PR report once
the complete standard CI build succeeds.
