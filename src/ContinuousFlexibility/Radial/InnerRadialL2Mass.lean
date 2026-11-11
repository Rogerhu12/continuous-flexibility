import ContinuousFlexibility.Radial.InnerPositiveGap
import ContinuousFlexibility.Statements.Radial
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Local fields in the actual radial L² measure

Every field is extended by zero into `radialHilbertMeasure D`. The
norm is computed from the physical density `12 * D.w r / r²`, with
no new abstract source measure and no comparison-norm hypothesis.
Only continuity on the closed interval is needed for the local field.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped InnerProductSpace

/-- The real L² norm uses the square of the actual representative. -/
theorem innerL2_norm_sq_eq_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

theorem innerRadialDensity_measurable (D : ReferenceData) (hw : Continuous D.w) :
    Measurable (fun r : ℝ => ENNReal.ofReal (12 * D.w r / r ^ 2)) :=
  ((measurable_const.mul hw.measurable).div (measurable_id.pow_const 2)).ennreal_ofReal

/-- Restricting the physical measure to an inner piece removes the
irrelevant outer core restriction, but keeps the same density. -/
theorem innerRadialHilbertMeasure_restrict (D : ReferenceData) {s : Set ℝ}
    (hs : MeasurableSet s) (hcore : s ⊆ radialCore D) :
    (radialHilbertMeasure D).restrict s =
      (volume.restrict s).withDensity (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2)) := by
  rw [radialHilbertMeasure, restrict_withDensity hs,
    Measure.restrict_restrict_of_subset hcore]

theorem innerRadialInterval_integrable_iff (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r) (g : ℝ → ℝ) :
    IntegrableOn g (Ioo a b) (radialHilbertMeasure D) ↔
      IntegrableOn (fun r => (12 * D.w r / r ^ 2) * g r) (Ioo a b) volume := by
  rw [IntegrableOn, innerRadialHilbertMeasure_restrict D measurableSet_Ioo hcore,
    integrable_withDensity_iff_integrable_smul' (innerRadialDensity_measurable D hw)
      (by simp)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [ENNReal.toReal_ofReal
    (div_nonneg (mul_nonneg (by norm_num) (hpos r hr)) (sq_nonneg _)), smul_eq_mul]

theorem innerRadialInterval_integral (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r) (g : ℝ → ℝ) :
    (∫ r in Ioo a b, g r ∂radialHilbertMeasure D) =
      ∫ r in Ioo a b, (12 * D.w r / r ^ 2) * g r := by
  rw [innerRadialHilbertMeasure_restrict D measurableSet_Ioo hcore,
    integral_withDensity_eq_integral_toReal_smul (innerRadialDensity_measurable D hw)
      (by simp)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  rw [ENNReal.toReal_ofReal
    (div_nonneg (mul_nonneg (by norm_num) (hpos r hr)) (sq_nonneg _)), smul_eq_mul]

theorem innerRadialInterval_sq_integral (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (hab : a ≤ b) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r) (u : ℝ → ℝ) :
    (∫ r in Ioo a b, u r ^ 2 ∂radialHilbertMeasure D) =
      innerRadialGapMass D.w u a b := by
  rw [innerRadialInterval_integral D hw hcore hpos, innerRadialGapMass,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- A continuous field on a compact inner interval gives an actual L²
field after extension by zero. -/
theorem innerRadialInterval_memLp (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r) (u : ℝ → ℝ)
    (hu : ContinuousOn u (Icc a b)) :
    MemLp ((Ioo a b).indicator u) 2 (radialHilbertMeasure D) := by
  apply (memLp_indicator_iff_restrict measurableSet_Ioo).mpr
  apply (memLp_two_iff_integrable_sq
    ((hu.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)).mpr
  apply (innerRadialInterval_integrable_iff D hw hcore hpos (fun r => u r ^ 2)).mpr
  have hρ : ContinuousOn (fun r : ℝ => 12 * D.w r / r ^ 2) (Icc a b) :=
    (continuousOn_const.mul hw.continuousOn).div (continuousOn_id.pow 2)
      (fun r hr => pow_ne_zero 2 (ha.trans_le hr.1).ne')
  exact ((hρ.mul (hu.pow 2)).integrableOn_Icc).mono_set Ioo_subset_Icc_self

/-- The local representative, in the same ambient radial Hilbert space
as all the other pieces. -/
def innerRadialIntervalToLp (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r) (u : ℝ → ℝ)
    (hu : ContinuousOn u (Icc a b)) : Lp ℝ 2 (radialHilbertMeasure D) :=
  (innerRadialInterval_memLp D hw ha hcore hpos u hu).toLp ((Ioo a b).indicator u)

theorem innerRadialIntervalToLp_ae (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r) (u : ℝ → ℝ)
    (hu : ContinuousOn u (Icc a b)) :
    innerRadialIntervalToLp D hw ha hcore hpos u hu =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator u :=
  MemLp.coeFn_toLp _

theorem innerRadialIntervalToLp_support (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r) (u : ℝ → ℝ)
    (hu : ContinuousOn u (Icc a b)) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b →
      innerRadialIntervalToLp D hw ha hcore hpos u hu r = 0 := by
  filter_upwards [innerRadialIntervalToLp_ae D hw ha hcore hpos u hu] with r hr
  intro hout
  rw [hr, indicator_of_notMem hout]

theorem innerRadialIntervalToLp_norm_sq (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r) (u : ℝ → ℝ)
    (hu : ContinuousOn u (Icc a b)) :
    ‖innerRadialIntervalToLp D hw ha hcore hpos u hu‖ ^ 2 =
      innerRadialGapMass D.w u a b := by
  rw [innerL2_norm_sq_eq_integral]
  calc
    _ = ∫ r, (Ioo a b).indicator (fun r => u r ^ 2) r ∂radialHilbertMeasure D := by
      apply integral_congr_ae
      filter_upwards [innerRadialIntervalToLp_ae D hw ha hcore hpos u hu] with r hr
      rw [hr]
      by_cases hmem : r ∈ Ioo a b
      · simp only [indicator_of_mem hmem]
      · simp only [indicator_of_notMem hmem, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    _ = ∫ r in Ioo a b, u r ^ 2 ∂radialHilbertMeasure D :=
      integral_indicator measurableSet_Ioo
    _ = _ := innerRadialInterval_sq_integral D hw hab hcore hpos u

end ContinuousFlexibility.Radial
