import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledSamplePrefix
import ContinuousFlexibility.Analysis.MaterialSampleShift

/-!
# The actual root-label sample and the retained positive sample

The inverse circle uses the original component number, whereas the
positive atlas uses the cell containing its retained midpoint. The N01
component-to-host displacement and the retained endpoint geometry give
one bounded index displacement between these two actual samples.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

/-- The circle slot of either genuine endpoint source remains a bounded
number of material cells from the supplied positive midpoint cell. -/
theorem n04PositiveGeometry_positiveSource_circle_index_bound
    (W : N04RealizationStart) (X : N04RealizationChoice W) :
    ∃ B : ℝ, 0 < B ∧ ∀ i side m, (X.src i side).val = some m →
      |(W.D.cellIndex m : ℝ) - W.D.cellIndex (X.cell i)| ≤ B := by
  obtain ⟨B₀, hB₀, hindex⟩ := W.through03.1.1.2.2.2.2.1
  obtain ⟨L, hL, hgap⟩ := retainedReference_positive_endpoint_midpointX_bound
    W.P W.metadata.selected W.metadata.first_two one_pos W.realizes W.hw W.coordinates
    W.through03.1.1.2.2.2.1 W.hT
  obtain ⟨D, hD, hcell, hclosed⟩ := material_cell_endpointX_closed_interval W.hT
  refine ⟨B₀ + L + 2 * D, by positivity, ?_⟩
  intro i side m hm
  have hend : n04PositiveEndpoint i side =
      (if side then W.C.left m else W.C.right m) := by
    simpa only [hm] using (X.src i side).property
  have hgeo := W.through03.1.1.2.2.2.1.1 m
  have hroot : n04PositiveEndpoint i side ∈ Icc (W.C.left m) (W.C.right m) := by
    rw [hend]
    cases side
    · exact ⟨hgeo.2.1.le, le_rfl⟩
    · exact ⟨le_rfl, hgeo.2.1.le⟩
  have hi := abs_le.mp (hindex m)
  have he := abs_le.mp (hclosed (W.C.left m) (W.C.right m) (W.C.cell m)
    hgeo.1 hgeo.2.1 hgeo.2.2 (W.host m) _ hroot)
  have hg := abs_le.mp (hgap i side)
  have hc := abs_le.mp (hcell (X.cell i) (n04PositiveMidpoint i) (X.cell_mem i))
  exact abs_le.mpr ⟨by linarith only [hi.2, he.2, hg.1, hc.1],
    by linarith only [hi.1, he.1, hg.2, hc.2]⟩

/-- Transfer any fixed material power at the actual inverse-circle slot
to the fixed positive sample. The height exponent is preserved exactly,
including the unweighted case `γ = 0`. -/
theorem n04PositiveGeometry_positiveSource_circle_material_weight
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (γ : ℝ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i side m, (X.src i side).val = some m →
      C * W.T.E0 (W.T.sample m) ^ A * W.T.H (W.T.sample m) ^ γ ≤
        B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
          W.U.H (W.U.sample (X.cell i)) ^ γ := by
  obtain ⟨L, hL, hindex⟩ := n04PositiveGeometry_positiveSource_circle_index_bound W X
  obtain ⟨K, P, hK, hP, htransfer⟩ :=
    materialSample_H_E0_rpow_of_index_sub_bound W.hT W.radial.1 γ hA hL.le
  obtain ⟨B₀, hB₀, hpack⟩ := coefficientEnvelope_pack (C * K) P
  let B : ℝ := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have hB₀B : B₀ ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro i side m hm
  have ht := htransfer m (X.cell i) (hindex i side m hm)
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  have hEU : W.T.E0 (W.T.sample (X.cell i)) ≤ E := le_enlargedMaterialData_E0 W.T _
  have hE : 1 ≤ E := (W.floor _).trans hEU
  have hH : 0 ≤ W.T.H (W.T.sample (X.cell i)) ^ γ := Real.rpow_nonneg
    (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
  have hcost : (C * K) * W.T.E0 (W.T.sample (X.cell i)) ^ P ≤ B * E ^ B := calc
    _ ≤ (C * K) * E ^ P := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans (W.floor _)) hEU hP) (mul_nonneg hC hK.le)
    _ ≤ B₀ * E ^ B₀ := hpack E hE
    _ ≤ B * E ^ B := mul_le_mul hB₀B (Real.rpow_le_rpow_of_exponent_le hE hB₀B)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  calc
    _ = C * (W.T.H (W.T.sample m) ^ γ * W.T.E0 (W.T.sample m) ^ A) := by ac_rfl
    _ ≤ C * (K * W.T.H (W.T.sample (X.cell i)) ^ γ *
        W.T.E0 (W.T.sample (X.cell i)) ^ P) := mul_le_mul_of_nonneg_left ht hC
    _ = ((C * K) * W.T.E0 (W.T.sample (X.cell i)) ^ P) *
        W.T.H (W.T.sample (X.cell i)) ^ γ := by ac_rfl
    _ ≤ (B * E ^ B) * W.T.H (W.T.sample (X.cell i)) ^ γ :=
      mul_le_mul_of_nonneg_right hcost hH

/-- The same comparison handles all parameter orders before a parameter
prefix is chosen; positive orders retain the exact sample height gain. -/
theorem n04PositiveGeometry_positiveSource_circle_parameter_weight
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (γ : ℝ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i side m, (X.src i side).val = some m → ∀ k,
      C * W.T.E0 (W.T.sample m) ^ A *
          parameterHeightWeight (W.T.H (W.T.sample m) ^ γ) k ≤
        B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
          parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ γ) k := by
  obtain ⟨B₀, hB₀, hzero⟩ :=
    n04PositiveGeometry_positiveSource_circle_material_weight W X 0 hA hC
  obtain ⟨B₁, hB₁, hpositive⟩ :=
    n04PositiveGeometry_positiveSource_circle_material_weight W X γ hA hC
  let B : ℝ := B₀ + B₁ + 1
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hB₀, hB₁]
  have hB₀B : B₀ ≤ B := by dsimp only [B]; linarith only [hB₁]
  have hB₁B : B₁ ≤ B := by dsimp only [B]; linarith only [hB₀]
  refine ⟨B, hB, ?_⟩
  intro i side m hm k
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hraise {A : ℝ} (hAB : A ≤ B) : A * E ^ A ≤ B * E ^ B :=
    mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hE hAB)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  by_cases hk : k = 0
  · subst k
    have hz : C * W.T.E0 (W.T.sample m) ^ A ≤ B₀ * E ^ B₀ := by
      simpa only [Real.rpow_zero, mul_one] using hzero i side m hm
    simpa only [parameterHeightWeight, if_pos rfl, mul_one] using hz.trans (hraise hB₀B)
  · have hH : 0 ≤ W.U.H (W.U.sample (X.cell i)) ^ γ := Real.rpow_nonneg
      (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
    simpa only [parameterHeightWeight, if_neg hk] using
      (hpositive i side m hm).trans (mul_le_mul_of_nonneg_right (hraise hB₁B) hH)

end ContinuousFlexibility.Analysis
