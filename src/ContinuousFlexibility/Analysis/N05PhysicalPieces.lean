module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Pointwise disjointness of the actual physical pieces

The almost-everywhere uniqueness in N04 forces disjointness of the open
radial intervals: a nonempty overlap would be an interval of positive
Lebesgue measure. Thus a source assembled by its physical piece agrees
pointwise with each local source throughout that piece.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory

theorem n05_intervals_disjoint_of_ae_unique {l r : ℕ → ℝ} {E : Set ℝ}
    (hE : volume E = 0)
    (hunique : ∀ x, x ∉ E → ∀ m n, x ∈ Ioo (l m) (r m) →
      x ∈ Ioo (l n) (r n) → m = n) :
    Pairwise (fun m n => Disjoint (Ioo (l m) (r m)) (Ioo (l n) (r n))) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro x hm hn
  let a : ℝ := max (l m) (l n)
  let b : ℝ := min (r m) (r n)
  have hax : a < x := max_lt hm.1 hn.1
  have hxb : x < b := lt_min hm.2 hn.2
  have hsub : Ioo a b ⊆ E := by
    intro y hy
    by_contra hyE
    apply hmn
    exact hunique y hyE m n
      ⟨(le_max_left _ _).trans_lt hy.1, hy.2.trans_le (min_le_left _ _)⟩
      ⟨(le_max_right _ _).trans_lt hy.1, hy.2.trans_le (min_le_right _ _)⟩
  have hpos : 0 < volume (Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (hax.trans hxb))
  have hzero : volume (Ioo a b) ≤ 0 := (measure_mono hsub).trans_eq hE
  exact (not_le_of_gt hpos) hzero

theorem n05_physicalPieces_pairwise_disjoint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε) :
    Pairwise (fun m n => Disjoint
      (Ioo (K.physicalLeft m) (K.physicalRight m))
      (Ioo (K.physicalLeft n) (K.physicalRight n))) := by
  have hinterval := h04.1.referenceBounds
  have hcover := h04.1.referencePartition
  obtain ⟨E, hE, hcover⟩ := hcover
  apply n05_intervals_disjoint_of_ae_unique hE
  intro r hr m n hm hn
  exact (hcover r ⟨(hinterval m).2.2 hm, hr⟩).unique hm hn

def n05PhysicalPieceIndex (S : PhysicalSpacesData) (K : CanonicalData S) (r : ℝ) : ℕ := by
  classical
  exact if h : ∃ m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) then h.choose else 0

theorem n05PhysicalPieceIndex_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {m : ℕ} {r : ℝ} (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    n05PhysicalPieceIndex S K r = m := by
  classical
  have hsome : ∃ n, r ∈ Ioo (K.physicalLeft n) (K.physicalRight n) := ⟨m, hr⟩
  rw [n05PhysicalPieceIndex, dite_eq_left hsome]
  by_contra hne
  exact Set.disjoint_left.mp (n05_physicalPieces_pairwise_disjoint h04 hne)
    hsome.choose_spec hr

end ContinuousFlexibility.Statements
