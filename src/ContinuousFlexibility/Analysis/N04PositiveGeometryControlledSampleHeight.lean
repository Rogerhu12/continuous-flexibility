import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledEndpoints
import ContinuousFlexibility.Analysis.N04RealizationPositiveSampleTransfer
import ContinuousFlexibility.Analysis.N01cMaterialAbsorption

/-!
# The exact height gain at the retained positive sample

Both physical endpoint sources are interior roots. Their complete positive
height exponent transfers to the already selected midpoint cell. The same
sample height has a global upper bound, needed when a finite product keeps
one copy of that height gain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Every fixed sample coefficient power is absorbed by the full positive
height gain, uniformly over the retained positive components. -/
theorem n04PositiveGeometry_sample_material_weight_bound
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ i,
      W.U.E0 (W.U.sample (X.cell i)) ^ A *
        W.U.H (W.U.sample (X.cell i)) ^ γ ≤ R := by
  have hU : IsMaterialData W.D W.U := isMaterialData_enlargedMaterialData W.radial.1 W.hT
  obtain ⟨R, hR, hbound⟩ := materialHeight_E0_weight_bounded hU hγ A
  refine ⟨R, hR, ?_⟩
  intro i
  simpa only [mul_comm] using hbound _ (materialSample_mem_interval W.radial.1 hU (X.cell i))

/-- A single radius makes any fixed material-weighted low variation
small at all positive samples. No component is selected first. -/
theorem n04PositiveGeometry_sample_material_smallness
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {γ A C η : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i t, |t| ≤ ε →
      C * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        W.U.H (W.U.sample (X.cell i)) ^ γ * |t| ≤ η := by
  obtain ⟨R, hR, hbound⟩ := n04PositiveGeometry_sample_material_weight_bound W X hγ A
  have hden : 0 < C * R + 1 := by positivity
  refine ⟨η / (C * R + 1), div_pos hη hden, ?_⟩
  intro i t ht
  have hscaled : C * W.U.E0 (W.U.sample (X.cell i)) ^ A *
      W.U.H (W.U.sample (X.cell i)) ^ γ ≤ C * R := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound i) hC
  have hweight : C * W.U.E0 (W.U.sample (X.cell i)) ^ A *
      W.U.H (W.U.sample (X.cell i)) ^ γ ≤ C * R + 1 :=
    hscaled.trans (le_add_of_nonneg_right zero_le_one)
  calc
    _ ≤ (C * R + 1) * (η / (C * R + 1)) :=
      mul_le_mul hweight ht (abs_nonneg t) hden.le
    _ = η := mul_div_cancel₀ η hden.ne'

/-- The height factor used in the parameter prefix is bounded before
the positive component is chosen. -/
theorem n04PositiveGeometry_sample_height_bound
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ RH : ℝ, 0 < RH ∧ ∀ i,
      0 ≤ W.U.H (W.U.sample (X.cell i)) ^ γ ∧
        W.U.H (W.U.sample (X.cell i)) ^ γ ≤ RH := by
  obtain ⟨RH, hRH, hbound⟩ := materialHeight_E0_weight_bounded W.hT hγ 0
  refine ⟨RH, hRH, ?_⟩
  intro i
  have hs : W.T.sample (X.cell i) ∈ Ioo W.D.a W.D.b :=
    materialSample_mem_interval W.radial.1 W.hT (X.cell i)
  refine ⟨Real.rpow_nonneg (W.hT.2.1 _ hs).2.1.le _, ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hbound _ hs

/-- A fixed pointwise polynomial coefficient at either actual endpoint
becomes one polynomial at the supplied sample. The exponent `γ` is exact. -/
theorem n04PositiveGeometry_positiveEndpoint_material_weight
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {γ A C : ℝ} (hγ : 0 < γ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i side,
      C * W.T.E0 (n04PositiveEndpoint i side) ^ A *
          W.T.H (n04PositiveEndpoint i side) ^ γ ≤
        B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
          W.U.H (W.U.sample (X.cell i)) ^ γ := by
  have hf : Continuous (deriv W.D.w) :=
    W.radial.1.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  obtain ⟨K, R, hK, hR, htransfer⟩ :=
    n04Realization_positive_midpoint_cell_H_E0_rpow W.hT W.radial.1 X.cell X.cell_mem hγ hA
  obtain ⟨B₀, hB₀, hpack⟩ := coefficientEnvelope_pack (C * K) R
  let B : ℝ := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have hB₀B : B₀ ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro i side
  have hlr : n04PositiveLeft i < n04PositiveRight i := (n04PositiveComponent_bounds hf i).2.1
  have hend : n04PositiveEndpoint i side ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) := by
    cases side
    · exact ⟨le_rfl, hlr.le⟩
    · exact ⟨hlr.le, le_rfl⟩
  have hcore : n04PositiveEndpoint i side ∈ Ioo W.D.a W.D.b :=
    (W.roots i side).1
  have ht := htransfer i (n04PositiveEndpoint i side) hend hcore
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  have hEU : W.T.E0 (W.T.sample (X.cell i)) ≤ E := le_enlargedMaterialData_E0 W.T _
  have hE : 1 ≤ E := (W.floor _).trans hEU
  have hs : W.T.sample (X.cell i) ∈ Ioo W.D.a W.D.b :=
    materialSample_mem_interval W.radial.1 W.hT (X.cell i)
  have hH : 0 ≤ W.T.H (W.T.sample (X.cell i)) ^ γ :=
    Real.rpow_nonneg (W.hT.2.1 _ hs).2.1.le _
  have hcost : (C * K) * W.T.E0 (W.T.sample (X.cell i)) ^ R ≤ B * E ^ B := calc
    _ ≤ (C * K) * E ^ R := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans (W.floor _)) hEU hR) (mul_nonneg hC hK.le)
    _ ≤ B₀ * E ^ B₀ := hpack E hE
    _ ≤ B * E ^ B := mul_le_mul hB₀B (Real.rpow_le_rpow_of_exponent_le hE hB₀B)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  calc
    _ = C * (W.T.H (n04PositiveEndpoint i side) ^ γ *
        W.T.E0 (n04PositiveEndpoint i side) ^ A) := by ring
    _ ≤ C * (K * W.T.H (W.T.sample (X.cell i)) ^ γ *
        W.T.E0 (W.T.sample (X.cell i)) ^ R) := mul_le_mul_of_nonneg_left ht hC
    _ = ((C * K) * W.T.E0 (W.T.sample (X.cell i)) ^ R) *
        W.T.H (W.T.sample (X.cell i)) ^ γ := by ring
    _ ≤ (B * E ^ B) * W.T.H (W.T.sample (X.cell i)) ^ γ :=
      mul_le_mul_of_nonneg_right hcost hH

end ContinuousFlexibility.Analysis
