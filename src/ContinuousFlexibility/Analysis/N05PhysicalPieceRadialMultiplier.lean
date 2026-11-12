import ContinuousFlexibility.Analysis.N05CanonicalOutputMultiplier

/-!
# Radial multipliers on the actual physical pieces

The disjoint N04 pieces turn smooth local radial coefficients into one
measurable physical field. The real cell association transfers a fixed
piece coefficient bound to every active reference localizer.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial

def n05PhysicalPieceRadialMultiplier (S : PhysicalSpacesData) (K : CanonicalData S)
    (b : ℕ → ℝ → ℝ) : ℝ → ℝ :=
  fun r => ∑' m, (Ioo (K.physicalLeft m) (K.physicalRight m)).indicator (b m) r

theorem n05PhysicalPieceRadialMultiplier_measurable
    (S : PhysicalSpacesData) (K : CanonicalData S) (b : ℕ → ℝ → ℝ)
    (hb : ∀ m, ContinuousOn (b m) (Ioo (K.physicalLeft m) (K.physicalRight m))) :
    Measurable (n05PhysicalPieceRadialMultiplier S K b) := by
  classical
  apply Measurable.tsum
  intro m
  exact (hb m).measurable_piecewise continuousOn_const measurableSet_Ioo

theorem n05PhysicalPieceRadialMultiplier_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (b : ℕ → ℝ → ℝ) {m : ℕ} {r : ℝ}
    (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    n05PhysicalPieceRadialMultiplier S K b r = b m r := by
  classical
  have hz : ∀ n, n ≠ m →
      (Ioo (K.physicalLeft n) (K.physicalRight n)).indicator (b n) r = 0 := by
    intro n hnm
    apply indicator_of_notMem
    intro hn
    exact Set.disjoint_left.mp (n05_physicalPieces_pairwise_disjoint h04 hnm) hn hr
  exact (tsum_eq_single m hz).trans (indicator_of_mem hr _)

theorem n05PhysicalPieceRadialMultiplier_eq_zero
    (S : PhysicalSpacesData) (K : CanonicalData S) (b : ℕ → ℝ → ℝ) {r : ℝ}
    (hr : ¬ ∃ m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    n05PhysicalPieceRadialMultiplier S K b r = 0 := by
  classical
  have hz (m : ℕ) :
      (Ioo (K.physicalLeft m) (K.physicalRight m)).indicator (b m) r = 0 :=
    indicator_of_notMem (fun hm => hr ⟨m, hm⟩) _
  simp only [n05PhysicalPieceRadialMultiplier, hz, tsum_zero]

theorem n05PhysicalPieceRadialMultiplier_cell_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {b : ℕ → ℝ → ℝ} {B A : ℝ} (hB : 0 < B) (hA : 0 ≤ A)
    (hb : ∀ m r, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
      |b m r| ^ 2 ≤ B * radialE (D.cellIndex (K.cell m)) ^ A) :
    ∃ C0 L0 : ℝ, 0 < C0 ∧ 0 < L0 ∧ ∀ j (p : PolarPoint),
      D.localizer j p.1 ≠ 0 →
        |n05PhysicalPieceRadialMultiplier S K b p.1| ^ 2 ≤
          C0 * Real.exp (L0 * radialQ (D.cellIndex j)) := by
  classical
  obtain ⟨window, _, hindex⟩ := n05_referencePiece_cell_index_bound hT hcoordinates
  obtain ⟨C0, hC0, hweight⟩ := n05_radialE_power_index_window A window hA
  refine ⟨B * C0, C0, mul_pos hB hC0, hC0, fun j p hpj => ?_⟩
  have hrj : p.1 ∈ D.cells j := hD.choose_spec.2.1.2.2.1 j hpj
  by_cases hp : ∃ m, p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
  · obtain ⟨m, hm⟩ := hp
    rw [n05PhysicalPieceRadialMultiplier_eq h04 _ hm]
    have hwindow : |(D.cellIndex (K.cell m) : ℝ) - (D.cellIndex j : ℝ)| ≤ window := by
      rw [abs_sub_comm]
      exact hindex m j p.1 hm hrj
    calc
      _ ≤ B * radialE (D.cellIndex (K.cell m)) ^ A := hb m p.1 hm
      _ ≤ B * (C0 * radialE (D.cellIndex j) ^ C0) :=
        mul_le_mul_of_nonneg_left
          (hweight (D.cellIndex (K.cell m)) (D.cellIndex j) hwindow) hB.le
      _ = _ := by
        rw [radialE, ← Real.exp_mul]
        rw [mul_comm (radialQ (D.cellIndex j)) C0]
        ring
  · rw [n05PhysicalPieceRadialMultiplier_eq_zero S K _ hp]
    simp only [abs_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity

end ContinuousFlexibility.Statements
