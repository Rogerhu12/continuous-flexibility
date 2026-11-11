import ContinuousFlexibility.Analysis.N01ReverseMaterialOrder
import ContinuousFlexibility.Analysis.ActualRadialCellComparison

/-!
# Fixed material-order transfer at every containing cell

The balanced constraint may select a containing cell independently for
each component. Any other containing cell has a uniformly close index.
Reserving half an extra material order for each comparison gives total
loss one, uniformly over all actual containing cells.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem N01Properties.material_order_transfer_at_every_actualCell
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {K A N : ℝ} (hK : 0 < K)
    (hbalanced : ∀ m, ∃ i : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells i ∧
      1 ≤ K * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ A *
        T.H (T.sample i) ^ (-(3 / 4 : ℝ)) * T.M (T.sample i) ^ N) :
    ∀ s : ℕ, ∃ Cs : ℝ, 0 < Cs ∧ ∀ m j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      T.M (T.sample m) ^ s ≤ Cs * T.M (T.sample j) ^ (s + 1) := by
  obtain ⟨B, hB, hlabel⟩ := hN.2.2.2.2.1
  obtain ⟨BC, hBC, hcommon⟩ := material_actualCells_index_bound hT
  intro s
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨K1, hK1, hb1⟩ := materialSample_M_rpow_of_reindexed_balanced_height_constraint
    hT hN.1.1 C.cell hB.le hlabel (A := A) (N := N)
      (by norm_num : (0 : ℝ) < 3 / 4) hK (Nat.cast_nonneg s) hhalf
  obtain ⟨K2, hK2, hb2⟩ := materialSample_M_rpow_of_index_sub_bound hT hN.1.1
    (show 0 ≤ (s : ℝ) + 1 / 2 by positivity) hhalf hBC.le
  refine ⟨K1 * K2, mul_pos hK1 hK2, fun m j hj => ?_⟩
  obtain ⟨i, hi, hraw⟩ := hbalanced m
  obtain ⟨r, hrl, hrh⟩ := exists_between (hN.2.2.2.1.1 m).2.1
  have hindex := hcommon i j r (hi ⟨hrl, hrh⟩) (hj ⟨hrl, hrh⟩)
  have h1 := hb1 m i hraw
  have h2 := hb2 i j hindex
  have hout : T.M (T.sample m) ^ (s : ℝ) ≤
      (K1 * K2) * T.M (T.sample j) ^ ((s : ℝ) + 1 / 2 + 1 / 2) :=
    h1.trans ((mul_le_mul_of_nonneg_left h2 hK1.le).trans_eq (by ring))
  have horder : (s : ℝ) + 1 / 2 + 1 / 2 = ((s + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  simpa only [horder, Real.rpow_natCast] using hout

end ContinuousFlexibility.Statements
