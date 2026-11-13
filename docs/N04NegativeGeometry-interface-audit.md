# NegativeGeometry: scope of the current-jet tower

The task is `N04RealizationNegativeGeometryObligation`, with the frozen
definitions in `Analysis/N04RealizationLeadCurrentSplit.lean` and
`Analysis/N04RealizationLeadCurrentData.lean`. This audit does not change
those definitions or the blueprint statement.

## The exact quantifier

The spatial regularity and both estimates in `CurrentJetDataOn` are guarded
by `P m`. The existence of the tower is not:

```lean
∃ J : ∀ m (i j : ℕ) (q : unitStrip),
  SmoothDirections (sectorNeighborhood S base ε ε)
    (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val),
  ...
```

Consequently, the negative-piece obligation also asks for genuine
parameter-smooth towers on every positive piece. The condition
`G.Admissible b ε` only supplies state-by-state
`WholePositiveTransportMatching 3` for the positive transport family;
the matching structure has no regularity hypothesis in the state parameter.

## Formal interface diagnostic

`Analysis/N04NegativeGeometryTowerAudit.lean` proves:

- A tower can be extracted at any piece, with no assumption `P m`.
- For `P = False`, the interface is equivalent to unrestricted existence
  of the towers; only the estimates and spatial-regularity clauses vanish.
- For every positive radius and every piece predicate, the spatially
  constant family `f z m q = |z.2|`, with zero reference, fails the
  interface. Restriction to the scalar line through zero would make the
  absolute value differentiable at zero.

This diagnostic alone is not a proof of the negation of the full gauge
obligation: a nonsmooth admissible gauge must also be supplied. The
distinction matters because the geometry families are prescribed functions,
not arbitrary inputs to `CurrentJetDataOn`.

## Link to the actual positive geometry

`Analysis/N04NegativeGeometryHeightPerturbation.lean` isolates two facts:

1. Multiplying `Q` by a smooth positive spatial multiplier, equal to one
   near the endpoint collars and the fixed middle, preserves
   `WholePositiveTransportMatching`. Bounds for the multiplier and its
   reciprocal enlarge only the positive bound constant. The lemma imposes
   no regularity in an external state parameter.
2. At a positive piece, the pulled height is the fixed reference height
   divided by `Q` at the fixed reference inverse-chart point. This formula
   includes the auxiliary-column replacement.

These facts permit a multiplier that switches from one to a nontrivial
interior bump when the scalar state parameter leaves zero.

## Complete obstruction to the frozen obligation

`Analysis/N04NegativeGeometryObstruction.lean` contains the assembled
statement

```lean
theorem n04NegativeGeometry_obligation_false :
    ¬ N04RealizationNegativeGeometryObligation
```

The argument uses an actual admissible gauge, not just an arbitrary scalar
family. Its compilation status is recorded below.

1. `N04NegativeGeometryAdmissibleExistence` constructs `G`, `b`, and
   `ε > 0` from the proved retained-start, optical, positive-reference and
   qualitative matching results. It uses neither open current-geometry
   subnode. The reference profile also has a positive component `i`.
2. Let `B` be the buffer supplied by `G.Admissible`. Set
   `aᵢ = (leftᵢ + B.centerLeft i) / 2` and
   `δᵢ = (B.centerLeft i - leftᵢ) / 4`. The existing smooth cutoff
   `χᵢ = positiveEndpointCutoff aᵢ δᵢ` is supported strictly between the
   left endpoint and the fixed middle, takes values in `[0,1]`, and is one
   at `aᵢ`. `N04NegativeGeometryInteriorFactor` certifies `φᵢ = 1 + χᵢ`.
3. Change only the positive height family to
   `Q' z i p = Q z i p * (if z.2 = 0 then 1 else φᵢ p)`.
   `N04NegativeGeometryGaugePerturbation` proves the resulting gauge `G'`
   is admissible on exactly the same neighborhood. Spatial smoothness,
   endpoint jets, periodicity, evenness and the fixed middle are retained;
   the permitted upper height bound doubles.
4. `N04NegativeGeometryGaugeValues` supplies a canonical `y : unitStrip`
   whose reference inverse point is `(aᵢ, 0)`. Let `m` be the corresponding
   positive piece. At this point the original and modified pulled heights
   satisfy `g(0) = f(0) > 0` and, on the scalar axis,
   `g(0,t) = f(0,t)/2` whenever `t ≠ 0`.
5. If the frozen NegativeGeometry obligation held, apply it once to `G`
   and once to `G'`. Intersect its two output neighborhoods using the
   maximum base order and the minimum positive radius, and choose the
   auxiliary column to be zero. The unguarded tower binder supplies
   zeroth-order directional towers for both pulled heights at this
   **positive** piece. It does not ask for a proof that the piece is
   negative.
6. `N04NegativeGeometryJumpObstruction` converts those towers into
   continuity. Taking the punctured limit at zero in `g = f/2` gives
   `f(0) = f(0)/2`, contradicting `f(0) > 0`. Subtracting different
   constant reference values in the two towers does not affect the
   continuity argument. Any positive-radius shrinking still contains
   the same punctured scalar germ.

This concerns the over-quantified subnode interface. It does not refute
the manuscript's existence assertion for a suitably chosen smooth atlas.

## Negative-piece reductions

`Analysis/N04NegativeGeometryReductions.lean` identifies `G.Neg η m` with
the retained negative summands of the whole-piece enumeration. It proves
that all non-auxiliary atoms, their current-minus-reference mixed spatial
derivatives, inverse points, and pulled height are precisely the original
typed-atlas expressions on `W.A X.e₀`. These identities hold without an
admissibility hypothesis on the positive family and without parameter
regularity of that family.

## Repair for the lead to assess

The intended piece-local interface would index the tower by a proof of
membership:

```lean
∃ J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
  SmoothDirections (sectorNeighborhood S base ε ε)
    (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val),
  ...
```

Then union selects the positive or negative tower on a piece belonging to
the corresponding family. With `P = True`, this recovers the unrestricted
tower needed by the assembly. The frozen interface has not been altered
on this branch, in accordance with `N04Realization-Common.md`.

## Validation

The source modules have no proof placeholders, added project axioms,
unsafe declarations, or raised heartbeat limits. The interface
counterexample, negative reductions, admissible existence, reference
positivity, jump obstruction and full refutation include guarded axiom
audits.

The first CI run, `43417103992` at `9344362a`, accepted the explicit
absolute-value counterexample and printed only `propext`,
`Classical.choice`, and `Quot.sound`; its module failed only because the
guard expected different line wrapping. The run also identified two
small elaboration repairs in the reduction/cancellation lemmas, now
addressed, and an inherited reference-chain failure in
`N03RootEndpointMaterialJets`; the lead's subsequent repair `3e7dcfcf`
has been merged.

The second run, `43418085638` at `eec2d271`, compiled the interface audit,
height-multiplier preservation, negative reductions, admissible-gauge
existence, and the gauge-value module. It found two pointwise-continuity
elaboration errors in the jump module and a reference-identity simplification
plus a large-record rewrite timeout in the gauge perturbation module.
These have been replaced by explicitly typed scalar equalities, without
raising heartbeat limits. The inherited reference-chain failure moved to
`ActualReferenceRootFiniteMaterialData.lean:92`
(`exists_bound_of_continuousOn` on a split line); the subnode does not
import that module. The complete obstruction audit remains pending until
its dependencies pass. The original NegativeGeometry blueprint theorem is
not marked complete.
