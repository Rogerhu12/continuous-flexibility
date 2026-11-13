import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledSampleHeight
import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightParameterPrefix

/-!
# Raw endpoint prefixes at the fixed positive sample

The retained endpoint-to-midpoint geometry controls the unweighted zeroth
parameter order as well as all positive orders. Combining this with the
exact height-weight transfer preserves `parameterHeightWeight` at every
parameter order, with one coefficient selected before either endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

theorem n04PositiveGeometry_positiveEndpoint_coefficient_weight
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i side,
      C * W.T.E0 (n04PositiveEndpoint i side) ^ A ≤
        B * W.U.E0 (W.U.sample (X.cell i)) ^ B := by
  obtain ⟨L, hL, hgap⟩ := retainedReference_positive_endpoint_midpointX_bound
    W.P W.metadata.selected W.metadata.first_two one_pos W.realizes W.hw W.coordinates
    W.through03.1.1.2.2.2.1 W.hT
  obtain ⟨D, hD, hcell, _hclosed⟩ := material_cell_endpointX_closed_interval W.hT
  obtain ⟨_KH, _AH, KE, AE, _hKH, _hAH, hKE, hAE, hcompare⟩ :=
    material_oneSided_endpoint_comparison W.hT W.radial.1 hA
      (show 0 ≤ L + 2 * D by positivity)
  have hdata := W.hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, _⟩ := hdata
  obtain ⟨B₀, hB₀, hpack⟩ := coefficientEnvelope_pack (C * KE) AE
  let B : ℝ := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have hB₀B : B₀ ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro i side
  have hm := abs_le.mp (hcell (X.cell i) (n04PositiveMidpoint i) (X.cell_mem i))
  have hs := abs_le.mp (hcell (X.cell i) (W.T.sample (X.cell i)) (hsample (X.cell i)))
  have hg := (abs_le.mp (hgap i side)).2
  have hshift : endpointX 1 (Statements.endpointDistance W.D (n04PositiveEndpoint i side)) ≤
      endpointX 1 (Statements.endpointDistance W.D (W.T.sample (X.cell i))) +
        (L + 2 * D) := by
    linarith only [hm.2, hs.1, hg]
  have hpoint := (hcompare (W.T.sample (X.cell i)) (n04PositiveEndpoint i side)
    (materialSample_mem_interval W.radial.1 W.hT (X.cell i)) (W.roots i side).1 hshift).2
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  have hEU : W.T.E0 (W.T.sample (X.cell i)) ≤ E := le_enlargedMaterialData_E0 W.T _
  have hE : 1 ≤ E := (W.floor _).trans hEU
  calc
    _ ≤ C * (KE * W.T.E0 (W.T.sample (X.cell i)) ^ AE) :=
      mul_le_mul_of_nonneg_left hpoint hC
    _ = (C * KE) * W.T.E0 (W.T.sample (X.cell i)) ^ AE := by ring
    _ ≤ (C * KE) * E ^ AE := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans (W.floor _)) hEU hAE) (mul_nonneg hC hKE.le)
    _ ≤ B₀ * E ^ B₀ := hpack E hE
    _ ≤ B * E ^ B := mul_le_mul hB₀B (Real.rpow_le_rpow_of_exponent_le hE hB₀B)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)

/-- One sample envelope transfers an entire finite or infinite parameter
prefix. Zeroth order has no height factor; every positive order keeps
the original exponent without loss. -/
theorem n04PositiveGeometry_positiveEndpoint_parameter_weight
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {γ A C : ℝ} (hγ : 0 < γ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i side k,
      C * W.T.E0 (n04PositiveEndpoint i side) ^ A *
          parameterHeightWeight (W.T.H (n04PositiveEndpoint i side) ^ γ) k ≤
        B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
          parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ γ) k := by
  obtain ⟨B₀, hB₀, hzero⟩ := n04PositiveGeometry_positiveEndpoint_coefficient_weight W X hA hC
  obtain ⟨B₁, hB₁, hpositive⟩ := n04PositiveGeometry_positiveEndpoint_material_weight W X hγ hA hC
  let B : ℝ := B₀ + B₁ + 1
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hB₀, hB₁]
  have hB₀B : B₀ ≤ B := by dsimp only [B]; linarith only [hB₁]
  have hB₁B : B₁ ≤ B := by dsimp only [B]; linarith only [hB₀]
  refine ⟨B, hB, ?_⟩
  intro i side k
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hraise {A : ℝ} (hAB : A ≤ B) : A * E ^ A ≤ B * E ^ B :=
    mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hE hAB)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  by_cases hk : k = 0
  · subst k
    simpa only [parameterHeightWeight, ite_true, mul_one] using
      (hzero i side).trans (hraise hB₀B)
  · have hH : 0 ≤ W.U.H (W.U.sample (X.cell i)) ^ γ := Real.rpow_nonneg
      (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
    simpa only [parameterHeightWeight, if_neg hk] using
      (hpositive i side).trans (mul_le_mul_of_nonneg_right (hraise hB₁B) hH)

end ContinuousFlexibility.Analysis
