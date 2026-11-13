# NegativeGeometry: scope of the current-jet tower

## Status after the subnode-interface repair

The audit below concerns the original draft at commit `3e23f7b3`.
The task rules now assign interface repairs to the subnode line itself.
The active definition has been repaired by indexing its directional towers
by `P m`; `mono`, `union`, and the final all-pieces assembly were adapted
at the same time. The original two audit modules are preserved under
`drafts/N04NegativeGeometry-original-interface/` because their negation
does not apply to the repaired definition. The final `N04cStatement` is
unchanged. Work continues on the actual negative-piece geometric towers;
the historical refutation is not a completion claim.

## Historical audit

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
family. The theorem compiled at commit `3e23f7b3179f582b843c424779a2388a1a43f958`,
and its guarded axiom audit passed with exactly `propext`,
`Classical.choice`, and `Quot.sound`.

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

## Validation and task status

[CI run 43420024812](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43420024812)
at `3e23f7b3179f582b843c424779a2388a1a43f958` records
`Built ContinuousFlexibility.Analysis.N04NegativeGeometryObstruction (11s)`
in its `build-log` artifact's `quick.log`. All eight supporting modules
were successfully replayed from their verified builds. The final module
contains this successful guarded audit:

```lean
/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_obligation_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_obligation_false
```

The nine added modules therefore compile, and the full negation has a
kernel-checked proof using only the permitted axioms. No source proof
placeholders, project axioms, unsafe declarations, or raised heartbeat
limits were added. No open current-geometry blueprint theorem is in the
refutation's import closure. The successful final audit checks the entire
proof dependency chain, including the actual admissible-gauge witness.

The original `Blueprint.N04RealizationNegativeGeometry` statement remains
open. This is a definitive refutation of its unchanged obligation, not a
completion claim for the original theorem. Its stated completion standard
cannot be met without a lead-authorized interface repair. Neither shared
definitions nor the blueprint statement were changed on this branch.

The verification run above failed solely at the inherited
`ActualReferenceRootFiniteMaterialData.lean:91–92` call. This module is
outside the refutation's import closure; responsibility for the ported
reference chain is assigned to the lead by `N04Realization-Common.md`.
The workflow's raw `modules compiled / total: 5464 / 5460` is a cached
artifact count containing stale modules, not a successful full build.
Repository-wide `statements open` was not recomputed because the full-build
and blueprint-status steps were skipped; this subnode's original statement
is open. The lead subsequently repaired that module in `cb14e791`, which
has been merged into this branch. The post-merge full-CI result is reported
in [PR #47](https://github.com/Rogerhu12/continuous-flexibility/pull/47).

The lead-owned call can be repaired by keeping the method dot adjacent to
its receiver:

```lean
  obtain ⟨W₀, hW₀⟩ :=
    (isCompact_Icc : IsCompact (Icc D.a D.b)).exists_bound_of_continuousOn
      hD.2.2.1.1.continuous.continuousOn
```

The split-line version produces the spurious `LE.le`/`Membership.mem`
method lookup errors; the subsequent destructuring error is a consequence.
The lead's merged repair uses the equivalent explicit
`IsCompact.exists_bound_of_continuousOn` call and also separates grading
simplifications into a scalar lemma. This subnode did not independently
edit the lead-owned file.
