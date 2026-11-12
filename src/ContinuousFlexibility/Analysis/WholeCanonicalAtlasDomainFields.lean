import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData

/-!
# Reference signs and current domain fields for the whole atlas

The negative flags are those of the original actual cut pairs. Positive
pieces are the genuine full positive intervals, including those that
touch an ambient endpoint. All fields refer to the same atlas record.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

private theorem wholeAtlas_old_negative_flag
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    (hcut : CanonicalReferenceCutPairs S C K) (j : ℕ × Bool) :
    K.positive (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1) = false := by
  rcases j with ⟨j, side⟩
  cases side
  · exact (hcut j).1
  · exact (hcut j).2.1

variable {D : ReferenceData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
  (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (F G : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ) {base : ℕ} {ε : ℝ}
  (hK : CanonicalGeometry D S C K base ε)
  (hcut : CanonicalReferenceCutPairs S C K) (hf : Continuous (deriv D.w))

include hK hf in
theorem n04WholeCanonicalAtlasData_referenceBounds (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    W.physicalLeft m < W.physicalRight m ∧ W.left m < W.right m ∧
      Ioo (W.physicalLeft m) (W.physicalRight m) ⊆ Ioo D.a D.b := by
  cases hi : e m with
  | inl j =>
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi] using
        hK.referenceBounds (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1)
  | inr i =>
      have hb := n04PositiveComponent_bounds hf i
      have hsub : Ioo (n04PositiveLeft i) (n04PositiveRight i) ⊆ Ioo D.a D.b :=
        fun r hr => ⟨hb.1.trans_lt hr.1, hr.2.trans_le hb.2.2⟩
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi] using
        And.intro hb.2.1 (And.intro hb.2.1 hsub)

include hf in
theorem n04WholeCanonicalAtlasData_referencePositive (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    W.positive m = true →
      ∀ r ∈ Ioo (W.physicalLeft m) (W.physicalRight m), 0 < deriv D.w r := by
  dsimp only
  intro hp r hr
  cases hi : e m with
  | inl j =>
      simp only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        n04WholePiecePositive, hi, Bool.false_eq_true] at hp
  | inr i =>
      apply n04PositiveComponent_interval_pos hf i
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi] using hr

include hK hcut in
theorem n04WholeCanonicalAtlasData_referenceNegative (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    W.positive m = false →
      ∀ r ∈ Ioo (W.physicalLeft m) (W.physicalRight m), deriv D.w r < 0 := by
  dsimp only
  intro hp r hr
  cases hi : e m with
  | inl j =>
      apply hK.referenceNegative
        (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1)
        (wholeAtlas_old_negative_flag hcut j) r
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi] using hr
  | inr i =>
      simp only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        n04WholePiecePositive, hi, Bool.true_eq_false] at hp

include hK hcut hf in
theorem n04WholeCanonicalAtlasData_domains
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    let Ω := physicalPieceOpen S W z m
    IsOpen Ω ∧ Ω.Nonempty ∧ Ω ⊆ annularOpen D ∧
    (∀ p : PolarPoint, p + (0, Real.pi) ∈ Ω ↔ p ∈ Ω) ∧
    (∀ p : PolarPoint, (p.1, -p.2) ∈ Ω ↔ p ∈ Ω) ∧
    (W.positive m = true → Ω = referencePhysicalPieceOpen S W m) ∧
    (∀ p ∈ Ω, W.positive m = true → 0 < deriv D.w p.1) ∧
    (∀ p ∈ Ω, W.positive m = false → deriv D.w p.1 < 0) := by
  cases hi : e m with
  | inl j =>
      have hneg := wholeAtlas_old_negative_flag hcut j
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, referencePhysicalPieceOpen, n04WholePiecePositive, hi, hneg] using
        hK.domains z hz hs (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1)
  | inr i =>
      let Ω := Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ)
      have hb := n04PositiveComponent_bounds hf i
      have hnonempty : Ω.Nonempty := by
        obtain ⟨x, hx⟩ := exists_between hb.2.1
        exact ⟨(x, 0), hx, mem_univ _⟩
      have hfields : IsOpen Ω ∧ Ω.Nonempty ∧ Ω ⊆ annularOpen D ∧
          (∀ p : PolarPoint, p + (0, Real.pi) ∈ Ω ↔ p ∈ Ω) ∧
          (∀ p : PolarPoint, (p.1, -p.2) ∈ Ω ↔ p ∈ Ω) ∧
          (true = true → Ω = Ω) ∧
          (∀ p ∈ Ω, true = true → 0 < deriv D.w p.1) ∧
          (∀ p ∈ Ω, true = false → deriv D.w p.1 < 0) := by
        refine ⟨isOpen_Ioo.prod isOpen_univ, hnonempty, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          exact ⟨⟨hb.1.trans_lt hp.1.1, hp.1.2.trans_le hb.2.2⟩, mem_univ _⟩
        · intro p
          simp only [Ω, mem_prod, Prod.fst_add, add_zero, mem_univ, and_true]
        · intro p
          rfl
        · intro _
          rfl
        · intro p hp _
          exact n04PositiveComponent_interval_pos hf i hp.1
        · intro p hp hfalse
          cases hfalse
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, referencePhysicalPieceOpen, n04WholePiecePositive, hi, Ω] using hfields

end ContinuousFlexibility.Analysis
