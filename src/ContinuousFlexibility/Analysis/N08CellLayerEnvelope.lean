module

public import ContinuousFlexibility.Analysis.N08CellLayerWeights

/-! # Sample envelope losses on the whole support of a cell cutoff -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem n08_point_sample_height_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ D.cells m →
      T.H r ^ (2 : ℝ) ≤ K * T.H (T.sample m) := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hE, henv, _, _, _, _, hcompare⟩ := hdata
  obtain ⟨C, A, hC, _, hCb⟩ := hcompare
  obtain ⟨U, hU, hUb⟩ := hE A
  obtain ⟨V, hV, hVb, _, _⟩ := henv 1 1 zero_lt_one
  obtain ⟨B, hB⟩ := hD
  refine ⟨C * U * V, mul_pos (mul_pos hC hU) hV, fun m r hr => ?_⟩
  have hcore : r ∈ Ioo D.a D.b := hB.2.1.2.2.2.1 m hr
  have hH : 0 < T.H r := (hT.2.1 r hcore).2.1
  have hs : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hB.2.1 m)).2.1
  have hratio : T.H r ≤ (C * T.E0 r ^ A) * T.H (T.sample m) :=
    (div_le_iff₀ hs).mp (hCb m r hr).2.2
  have hpay : T.H r * T.E0 r ^ A ≤ U * V := by
    calc
      _ ≤ T.H r * (U * T.M r) := mul_le_mul_of_nonneg_left (hUb r hcore) hH.le
      _ = U * (T.H r * T.M r) := by ring
      _ ≤ U * V := mul_le_mul_of_nonneg_left
        (by simpa only [Real.rpow_one] using hVb r hcore) hU.le
  rw [Real.rpow_two, pow_two]
  calc
    _ ≤ T.H r * ((C * T.E0 r ^ A) * T.H (T.sample m)) :=
      mul_le_mul_of_nonneg_left hratio hH.le
    _ = C * (T.H r * T.E0 r ^ A) * T.H (T.sample m) := by ring
    _ ≤ C * (U * V) * T.H (T.sample m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpay hC.le) hs.le
    _ = _ := by ring

theorem n08CellLayerBand_reverse_height_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) {A : ℝ} (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ n08CellLayerBand D A m →
      T.H r ^ (2 : ℝ) ≤ K * T.H (T.sample m) ^ (1 / 16 : ℝ) := by
  obtain ⟨K, hK, hKb⟩ := n08_point_sample_height_bound hD hT
  obtain ⟨B, hB, hBb⟩ := n08CellLayerBand_index_bound hD hA
  obtain ⟨L, hL, hLb⟩ := n08_twoSample_point_height_bound hD hT hB zero_lt_one
  obtain ⟨C, hC⟩ := hD
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _⟩ := hdata
  refine ⟨K * L, mul_pos hK hL, fun m r hr => ?_⟩
  have hcore : r ∈ Ioo D.a D.b :=
    Analysis.intervalEndpointLayer_subset_Ioo (n08CellLayerInner_pos hA _) hr
  obtain ⟨j, hrj⟩ := hC.2.1.exists_cell hcore
  have hj : T.H (T.sample j) ≤ L * T.H (T.sample m) ^ (1 / 16 : ℝ) := by
    simpa only [Real.rpow_one] using hLb j m (T.sample m) (hsamp m)
      ((abs_sub_comm _ _).trans_le (hBb m j r hr hrj))
  exact (hKb j r hrj).trans ((mul_le_mul_of_nonneg_left hj hK.le).trans_eq (by ring))

theorem n08CellLayerBand_envelope_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) {A : ℝ} (hA : 0 < A) (N : ℝ) :
    ∃ K R : ℝ, 0 < K ∧ 0 ≤ R ∧ ∀ m r, r ∈ n08CellLayerBand D A m →
      T.M (T.sample m) ^ N ≤ K * T.M r ^ R := by
  obtain ⟨C, hC, hCb⟩ := n08CellLayerBand_reverse_height_bound hD hT hA
  obtain ⟨K, R, hK, hR, hKb⟩ := n08_material_envelope_power_comparison hT
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1 / 16) hC N
  obtain ⟨B, hB⟩ := hD
  refine ⟨K, R, hK, hR, fun m r hr => ?_⟩
  exact hKb r (T.sample m)
    (Analysis.intervalEndpointLayer_subset_Ioo (n08CellLayerInner_pos hA _) hr)
    (materialSample_mem_radialCore hT hB.2.1 m) (hCb m r hr)

end ContinuousFlexibility.Statements
