import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeAtomTransport
import ContinuousFlexibility.Analysis.CanonicalAuxiliaryAtomPreservation

/-!
# The negative part of a Realization gauge is the retained typed atlas

These identities hold for every state and every spatial point.  They need
neither admissibility of the positive transport family nor any regularity
assumption on that family.  The right-hand sides use the original typed
atlas and are independent of the auxiliary-column replacement.

In particular, spatial jets of a current-minus-reference geometry atom on
a negative piece are exactly those of the original negative half.  This
is a reduction of the actual functions, not an estimate for a different
choice of chart or inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements CanonicalGeometry

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The old typed index of a retained negative half. -/
def negativeIndex (j : ℕ × Bool) : ℕ := G.X.e₀.symm (.inl j)

/-- Selecting a side of the old cut pair gives that same typed index. -/
theorem negativeIndex_eq_cut (j : ℕ × Bool) :
    G.negativeIndex j =
      if j.2 then ((G.W.A G.X.e₀).cutPair j.1).2
      else ((G.W.A G.X.e₀).cutPair j.1).1 := by
  rcases j with ⟨m, side⟩
  cases side <;> rfl

theorem negativeIndex_negative (j : ℕ × Bool) :
    (G.W.A G.X.e₀).positive (G.negativeIndex j) = false := by
  simp only [negativeIndex, N04RealizationStart.A, n04bActualTypedAtlas,
    n04bTypedAtlasData_positive, Equiv.apply_symm_apply, n04TypedPiecePositive]

variable (η : (G.W.S.height (3 / 4 : ℝ)).Space)

/-- The predicate `Neg` singles out exactly the retained negative indices. -/
theorem neg_iff_inl (m : ℕ) :
    G.Neg η m ↔ ∃ j : ℕ × Bool, G.e m = .inl j := by
  constructor
  · intro hm
    cases hi : G.e m with
    | inl j => exact ⟨j, rfl⟩
    | inr i =>
        change n04WholePiecePositive (G.e m) = false at hm
        rw [hi] at hm
        cases hm
  · intro hm
    exact hm.elim fun j hi => by
      change n04WholePiecePositive (G.e m) = false
      rw [hi]
      rfl

/-- The same endpoints, sample, chart, inverse, height and operator fields
are retained, including after replacing the auxiliary source column. -/
theorem negative_fields (z : AnnularState G.W.S × ℝ)
    (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j) :
    let K := G.W.A G.X.e₀
    let k := G.negativeIndex j
    (G.V η).left m = K.left k ∧ (G.V η).right m = K.right k ∧
      (G.V η).physicalLeft m = K.physicalLeft k ∧
      (G.V η).physicalRight m = K.physicalRight k ∧
      physicalPieceOpen (G.S η) (G.V η) z m = physicalPieceOpen G.W.S K z k ∧
      (G.V η).cell m = K.cell k ∧ (G.V η).positive m = false ∧
      (G.V η).chart z m = K.chart z k ∧
      (G.V η).inverseChart z m = K.inverseChart z k ∧
      (G.V η).height z m = K.height z k ∧
      (G.V η).coefficients z m = K.coefficients z k ∧
      (G.V η).potential z m = K.potential z k := by
  have h := n04WholeReferenceGaugeAtlasData_negative_fields
    G.W.C G.W.L (G.W.A G.X.e₀) G.e G.X.cell
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i))
    (fun i p => G.H i p.1) G.τ G.σ G.Q G.N z m j hi
  rw [← G.negativeIndex_eq_cut j] at h
  exact h

/-- Every non-auxiliary atom on the negative piece is the original atom,
with precisely the same enlarged material data. -/
theorem negative_atom (z : AnnularState G.W.S × ℝ)
    (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j)
    (a : Atom) (ha : a ≠ .auxiliaryColumn) :
    atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m a =
      atom G.W.D G.W.U G.W.S G.W.C G.W.L (G.W.A G.X.e₀) z
        (G.negativeIndex j) a := by
  have haux := canonicalAtom_replaceAuxiliaryColumn_of_ne
    G.W.D G.W.U G.W.S G.W.C G.W.L
    (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N) η z m a ha
  have hnegative := G.negativeIndex_negative j
  rw [G.negativeIndex_eq_cut j] at hnegative
  have hwhole := n04WholeReferenceGaugeAtlasData_negative_atom
    G.W.U G.W.C G.W.L (G.W.A G.X.e₀) G.e G.X.cell
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i))
    (fun i p => G.H i p.1) G.τ G.σ G.Q G.N z m j hi hnegative a
  rw [← G.negativeIndex_eq_cut j] at hwhole
  exact haux.trans hwhole

/-- Current sector families have the same negative-half formula, before
any auxiliary column is chosen. -/
theorem negative_atomFamily (z : Parameter G.W.S)
    (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j)
    (a : Atom) (ha : a ≠ .auxiliaryColumn) :
    G.atomFamily η a z m =
      atom G.W.D G.W.U G.W.S G.W.C G.W.L (G.W.A G.X.e₀)
        (liftSectorParameter G.W.S G.W.C z) (G.negativeIndex j) a :=
  G.negative_atom η (liftSectorParameter G.W.S G.W.C z) m j hi a ha

theorem negative_atomRef (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j)
    (a : Atom) (ha : a ≠ .auxiliaryColumn) :
    G.atomRef η a m =
      atom G.W.D G.W.U G.W.S G.W.C G.W.L (G.W.A G.X.e₀)
        (G.W.C.referenceState, 0) (G.negativeIndex j) a :=
  G.negative_atom η (G.W.C.referenceState, 0) m j hi a ha

/-- Consequently all mixed spatial derivatives of the actual difference
agree, not just its zeroth order values. -/
theorem negative_atomDifference_mixedDerivative (z : Parameter G.W.S)
    (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j)
    (a : Atom) (ha : a ≠ .auxiliaryColumn) (r s : ℕ) (q : PolarPoint) :
    mixedDerivative r s (fun y => G.atomFamily η a z m y - G.atomRef η a m y) q =
      mixedDerivative r s (fun y =>
        atom G.W.D G.W.U G.W.S G.W.C G.W.L (G.W.A G.X.e₀)
          (liftSectorParameter G.W.S G.W.C z) (G.negativeIndex j) a y -
        atom G.W.D G.W.U G.W.S G.W.C G.W.L (G.W.A G.X.e₀)
          (G.W.C.referenceState, 0) (G.negativeIndex j) a y) q := by
  rw [G.negative_atomFamily η z m j hi a ha, G.negative_atomRef η m j hi a ha]

/-- The canonical unit point is formed from the retained endpoints. -/
theorem negative_canonicalUnitPoint (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j) :
    canonicalUnitPoint (G.V η) m =
      canonicalUnitPoint (G.W.A G.X.e₀) (G.negativeIndex j) := by
  have h := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  funext q
  simp only [canonicalUnitPoint, h.1, h.2.1]

theorem negative_pulledPoint (z : AnnularState G.W.S × ℝ)
    (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j) (q : PolarPoint) :
    G.pulledPoint η z m q =
      (G.W.A G.X.e₀).inverseChart z (G.negativeIndex j)
        (canonicalUnitPoint (G.W.A G.X.e₀) (G.negativeIndex j) q) := by
  have h := G.negative_fields η z m j hi
  change (G.V η).inverseChart z m (canonicalUnitPoint (G.V η) m q) = _
  rw [h.2.2.2.2.2.2.2.2.1, G.negative_canonicalUnitPoint η m j hi]

/-- Pulling the height back by the inverse chart commutes with retaining
the negative half and with the auxiliary-column replacement. -/
theorem negative_pulledHeight (z : Parameter G.W.S)
    (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j) (q : PolarPoint) :
    G.pulledHeight η z m q =
      (G.W.A G.X.e₀).height (liftSectorParameter G.W.S G.W.C z) (G.negativeIndex j)
        ((G.W.A G.X.e₀).inverseChart (liftSectorParameter G.W.S G.W.C z)
          (G.negativeIndex j)
          (canonicalUnitPoint (G.W.A G.X.e₀) (G.negativeIndex j) q)) := by
  have h := G.negative_fields η (liftSectorParameter G.W.S G.W.C z) m j hi
  change (G.V η).height (liftSectorParameter G.W.S G.W.C z) m
    (G.pulledPoint η (liftSectorParameter G.W.S G.W.C z) m q) = _
  rw [h.2.2.2.2.2.2.2.2.2.1,
    G.negative_pulledPoint η (liftSectorParameter G.W.S G.W.C z) m j hi q]

theorem negative_pulledHeightRef
    (m : ℕ) (j : ℕ × Bool) (hi : G.e m = .inl j) (q : PolarPoint) :
    G.pulledHeightRef η m q =
      (G.W.A G.X.e₀).height (G.W.C.referenceState, 0) (G.negativeIndex j)
        ((G.W.A G.X.e₀).inverseChart (G.W.C.referenceState, 0) (G.negativeIndex j)
          (canonicalUnitPoint (G.W.A G.X.e₀) (G.negativeIndex j) q)) := by
  have h := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  exact (congrFun h.2.2.2.2.2.2.2.2.2.1
      (G.pulledPoint η (G.W.C.referenceState, 0) m q)).trans
    (congrArg ((G.W.A G.X.e₀).height (G.W.C.referenceState, 0) (G.negativeIndex j))
      (G.negative_pulledPoint η (G.W.C.referenceState, 0) m j hi q))

end N04RealizationGauge

end ContinuousFlexibility.Analysis

/--
info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negative_atomDifference_mixedDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negative_atomDifference_mixedDerivative

/--
info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negative_pulledHeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negative_pulledHeight
