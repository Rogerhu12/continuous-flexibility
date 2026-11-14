module

public import ContinuousFlexibility.Analysis.MaterialSampleWeightedConstraint
public import ContinuousFlexibility.Analysis.ActualRadialCellComparison
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Full return-label weight transfer at every actual containing cell

The balanced constraint may choose one actual radial cell for each
negative component. The common-point index comparison then transfers
the complete height and material weight to any containing cell with
two additional orders. All losses are fixed before the order `s`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem N01Properties.weighted_order_transfer_at_every_actualCell
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {K A N : ℝ} (hK : 0 < K)
    (hbalanced : ∀ m, ∃ i : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells i ∧
      1 ≤ K * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ A *
        T.H (T.sample i) ^ (-(3 / 4 : ℝ)) * T.M (T.sample i) ^ N) :
    ∃ weightLoss : ℕ, ∀ s : ℕ, ∃ Cs : ℝ, 0 < Cs ∧ ∀ m j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * T.M (T.sample m) ^ s ≤
        Cs * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) *
          T.M (T.sample j) ^ (s + weightLoss) := by
  obtain ⟨B, hB, hlabel⟩ := hN.2.2.2.2.1
  obtain ⟨BC, hBC, hcommon⟩ := material_actualCells_index_bound hT
  obtain ⟨L, hfull⟩ := materialSample_H_M_pow_of_reindexed_balanced_height_constraint
    hT hN.1.1 C.cell hB.le hlabel (A := A) (N := N)
      (by norm_num : (0 : ℝ) < 3 / 4) hK
  refine ⟨L + 2, fun s => ?_⟩
  obtain ⟨K1, hK1, htransfer⟩ := hfull s
  obtain ⟨K2, hK2, hshift⟩ := materialSample_H_M_rpow_of_index_sub_bound
    hT hN.1.1 (-(3 / 4 : ℝ)) (Nat.cast_nonneg (s + L)) hBC.le
  refine ⟨K1 * K2, mul_pos hK1 hK2, fun m j hj => ?_⟩
  obtain ⟨i, hi, hraw⟩ := hbalanced m
  obtain ⟨r, hrl, hrh⟩ := exists_between (hN.2.2.2.1.1 m).2.1
  have hindex := hcommon i j r (hi ⟨hrl, hrh⟩) (hj ⟨hrl, hrh⟩)
  have horder : ((s + L : ℕ) : ℝ) + 2 = ((s + (L + 2) : ℕ) : ℝ) := by
    push_cast
    ring
  have hshift' : T.H (T.sample i) ^ (-(3 / 4 : ℝ)) * T.M (T.sample i) ^ (s + L) ≤
      K2 * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.M (T.sample j) ^ (s + (L + 2)) := by
    simpa only [horder, Real.rpow_natCast] using hshift i j hindex
  calc
    _ ≤ K1 * (T.H (T.sample i) ^ (-(3 / 4 : ℝ)) * T.M (T.sample i) ^ (s + L)) :=
      (htransfer m i hraw).trans_eq (by ring)
    _ ≤ K1 * (K2 * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) *
        T.M (T.sample j) ^ (s + (L + 2))) := mul_le_mul_of_nonneg_left hshift' hK1.le
    _ = _ := by ring

end ContinuousFlexibility.Statements
