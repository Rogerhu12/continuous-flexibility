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
interior bump when the scalar state parameter leaves zero. The branch is
developing the admissibility and nonsmoothness argument explicitly rather
than assuming that the interface diagnostic by itself settles the node.

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
counterexample and the negative reductions include guarded axiom audits.
Compilation and the complete branch CI are pending; the original
NegativeGeometry blueprint theorem is not marked complete.
