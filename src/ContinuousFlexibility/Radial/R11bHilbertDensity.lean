module

public import ContinuousFlexibility.Radial.R11bDensityQuotient
public import ContinuousFlexibility.Statements.Radial

/-!
# The actual radial Hilbert density

On the finite radial core the density 12w/r² is positive and bounded.
Its inverse square root differs from w⁻¹/² by the bounded factor r/√12.
These facts transfer physical radial L² fields and sources to the actual
radial Hilbert measure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements

theorem r11b_radial_density_measurable {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) :
    Measurable (fun r => 12 * D.w r / r ^ 2) :=
  (measurable_const.mul hgeom.2.2.1.1.continuous.measurable).div
    (measurable_id.pow_const 2)

theorem r11b_radial_density_pos_ae {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) :
    ∀ᵐ r ∂volume.restrict (radialCore D), 0 < 12 * D.w r / r ^ 2 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hr0 : 0 < r := hgeom.1.trans hr.1
  have hw : 0 < D.w r := hgeom.2.2.2.2.1 r hr
  positivity

theorem r11b_radial_density_bounded {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) :
    ∃ C : ℝ, ∀ᵐ r ∂volume.restrict (radialCore D),
      12 * D.w r / r ^ 2 ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).bddAbove_image
    hgeom.2.2.1.1.continuous.continuousOn
  let C : ℝ := 12 * |M| / D.a ^ 2
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (sq_nonneg _)
  refine ⟨C, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hr0 : 0 < r := hgeom.1.trans hr.1
  have hwM : D.w r ≤ |M| :=
    (hM ⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩).trans (le_abs_self M)
  have hsquare : D.a ^ 2 ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.1.le) (add_nonneg hr0.le hgeom.1.le)]
  have hcancel : C * D.a ^ 2 = 12 * |M| := by
    dsimp [C]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hgeom.1.ne')
  apply (div_le_iff₀ (sq_pos_of_pos hr0)).mpr
  calc
    12 * D.w r ≤ 12 * |M| := mul_le_mul_of_nonneg_left hwM (by norm_num)
    _ = C * D.a ^ 2 := hcancel.symm
    _ ≤ C * r ^ 2 := mul_le_mul_of_nonneg_left hsquare hC

theorem r11b_sqrt_inverse_radial_density (w r : ℝ) (hr : 0 ≤ r) :
    sqrt ((12 * w / r ^ 2)⁻¹) = (r / sqrt 12) * sqrt (w⁻¹) := by
  rw [inv_div, sqrt_div (sq_nonneg r), sqrt_sq hr,
    sqrt_mul (by norm_num : (0 : ℝ) ≤ 12), sqrt_inv]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem r11b_memLp_radialHilbert_of_memLp {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (radialCore D))) :
    MemLp f 2 (radialHilbertMeasure D) := by
  obtain ⟨C, hC⟩ := r11b_radial_density_bounded hgeom
  exact r11b_memLp_withDensity_ofReal_of_bound
    (r11b_radial_density_measurable hgeom).aemeasurable
    ((r11b_radial_density_pos_ae hgeom).mono (fun r hr => hr.le)) hC hf

theorem r11b_memLp_div_radialDensity_of_inverse_sqrt {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {f : ℝ → ℝ}
    (hf : MemLp (fun r => sqrt ((D.w r)⁻¹) * f r)
      2 (volume.restrict (radialCore D))) :
    MemLp (fun r => f r / (12 * D.w r / r ^ 2)) 2 (radialHilbertMeasure D) := by
  apply (r11b_memLp_div_withDensity_ofReal_iff
    (r11b_radial_density_measurable hgeom).aemeasurable
    (r11b_radial_density_pos_ae hgeom)).mpr
  have hrad : AEStronglyMeasurable (fun r : ℝ => r / sqrt 12)
      (volume.restrict (radialCore D)) :=
    (measurable_id.div measurable_const).aestronglyMeasurable
  have hmul : MemLp (fun r => (r / sqrt 12) * (sqrt ((D.w r)⁻¹) * f r))
      2 (volume.restrict (radialCore D)) := by
    apply hf.of_le_mul (c := D.b / sqrt 12) (hrad.mul hf.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hr0 : 0 ≤ r := (hgeom.1.trans hr.1).le
    change ‖(r / sqrt 12) * (sqrt ((D.w r)⁻¹) * f r)‖ ≤
      (D.b / sqrt 12) * ‖sqrt ((D.w r)⁻¹) * f r‖
    rw [norm_mul, Real.norm_of_nonneg (div_nonneg hr0 (sqrt_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hr.2.le (sqrt_nonneg _)) (norm_nonneg _)
  apply MemLp.ae_eq _ hmul
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [r11b_sqrt_inverse_radial_density _ _ (hgeom.1.trans hr.1).le]
  ring

end ContinuousFlexibility.Radial
