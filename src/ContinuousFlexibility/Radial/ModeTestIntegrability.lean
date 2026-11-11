import ContinuousFlexibility.Radial.ModeDensityDerivative
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Integrable modal weak tests

The normalized Jacobi test belongs to the actual Hilbert space. The proof
uses the global Glaeser estimate for the nonnegative profile, so ordinary
support at the singular radial endpoints is sufficient. Both sides of the
weak equation are bounded linear pairings on the modal Hilbert space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

theorem matching_memLp_of_continuousOn {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {g : ℝ → ℝ} (hg : Measurable g) (hc : ContinuousOn g (Icc D.a D.b))
    (p : ENNReal) : MemLp g p (radialHilbertMeasure D) := by
  letI : IsFiniteMeasure (radialHilbertMeasure D) := radialHilbertMeasure_isFinite hD
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  apply (radialHilbertMeasure_ae_iff hD).mpr
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  exact hC (mem_image_of_mem _ ⟨hr.1.le, hr.2.le⟩)

/-- The logarithmic derivative need not be bounded, but is square integrable
against the actual vanishing Hilbert density. -/
theorem matchingLogDerivative_memLp {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    MemLp (fun r => deriv D.w r / D.w r) 2 (radialHilbertMeasure D) := by
  have hg := matchingProfileGeometry hD
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hm : Measurable (fun r => deriv D.w r / D.w r) :=
    hd.continuous.measurable.div hw.continuous.measurable
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (matchingDensity_integrable_iff hD _).mpr
  obtain ⟨C, hC, hbound⟩ := matchingProfile_deriv_sq_bound hD
  have hfinite : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    change IsFiniteMeasure (volume.restrict (Ioo D.a D.b))
    infer_instance
  letI := hfinite
  apply (integrable_const (12 * C / D.a ^ 2)).mono'
    (by
      have he :
          (fun r => matchingDensity D r * (deriv D.w r / D.w r) ^ 2) =
            matchingDensity D *
              ((fun r => deriv D.w r / D.w r) * (fun r => deriv D.w r / D.w r)) := by
        funext r
        simp only [Pi.mul_apply, pow_two]
      rw [he]
      exact ((matchingDensity_measurable hD).mul (hm.mul hm)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  have hw0 : 0 < D.w r := hg.2.2.2.2.1 r hr
  have hr0 : 0 < r := lt_trans hg.1 hr.1
  have hratio : (deriv D.w r) ^ 2 / D.w r ≤ C :=
    (div_le_iff₀ hw0).mpr (hbound r)
  have hden : D.a ^ 2 ≤ r ^ 2 := by nlinarith [hg.1, hr.1, sq_nonneg (r - D.a)]
  have hinv : 12 / r ^ 2 ≤ 12 / D.a ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hg.1) hden
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (matchingDensity_pos hD hr).le (sq_nonneg _))]
  calc
    matchingDensity D r * (deriv D.w r / D.w r) ^ 2 =
        (12 / r ^ 2) * ((deriv D.w r) ^ 2 / D.w r) := by
      unfold matchingDensity
      field_simp [hw0.ne', hr0.ne']
      <;> ring
    _ ≤ (12 / r ^ 2) * C :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ (12 / D.a ^ 2) * C := mul_le_mul_of_nonneg_right hinv hC.le
    _ = 12 * C / D.a ^ 2 := by ring

theorem matchingJacobi_expansion {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : ℕ) (r : ℝ) :
    radialJacobi ((j : ℝ) ^ 2) D.w ψ r =
      D.w r * deriv (deriv ψ) r +
        deriv D.w r * (deriv ψ r - (j : ℝ) ^ 2 / r * ψ r) := by
  have hw : ContDiff ℝ ∞ D.w := (matchingProfileGeometry hD).2.2.1.1
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  unfold radialJacobi
  rw [deriv_fun_mul (hw.differentiable (by simp) r) (hdψ.differentiable (by simp) r)]
  ring

def matchingJacobiTest (D : ReferenceData) (j : ℕ) (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  radialJacobi ((j : ℝ) ^ 2) D.w ψ r / matchingDensity D r

theorem matchingJacobiTest_memLp {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : ℕ) :
    MemLp (matchingJacobiTest D j ψ) 2 (radialHilbertMeasure D) := by
  have hg := matchingProfileGeometry hD
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hddψ : ContDiff ℝ ∞ (deriv (deriv ψ)) :=
    (contDiff_infty_iff_deriv.mp hdψ).2
  let q₁ : ℝ → ℝ := fun r => r ^ 2 / 12 * deriv (deriv ψ) r
  let q₂ : ℝ → ℝ := fun r =>
    r ^ 2 / 12 * (deriv ψ r - (j : ℝ) ^ 2 / r * ψ r)
  have hq₁m : Measurable q₁ := by
    dsimp [q₁]
    fun_prop
  have hq₁c : Continuous q₁ :=
    ((continuous_id.pow 2).div_const 12).mul hddψ.continuous
  have hq₁ : MemLp q₁ 2 (radialHilbertMeasure D) :=
    matching_memLp_of_continuousOn hD hq₁m hq₁c.continuousOn 2
  have hq₂m : Measurable q₂ := by
    have hψm : Measurable ψ := hψ.continuous.measurable
    have hdψm : Measurable (deriv ψ) := hdψ.continuous.measurable
    dsimp [q₂]
    fun_prop
  have hratio : ContinuousOn (fun r : ℝ => (j : ℝ) ^ 2 / r) (Icc D.a D.b) := by
    apply continuous_const.continuousOn.div continuous_id.continuousOn
    intro r hr
    exact ne_of_gt (lt_of_lt_of_le hg.1 hr.1)
  have hq₂c : ContinuousOn q₂ (Icc D.a D.b) :=
    ((continuous_id.pow 2).div_const 12).continuousOn.mul
      (hdψ.continuous.continuousOn.sub (hratio.mul hψ.continuous.continuousOn))
  have hq₂ : MemLp q₂ ⊤ (radialHilbertMeasure D) :=
    matching_memLp_of_continuousOn hD hq₂m hq₂c ⊤
  have hmul : MemLp (fun r => q₂ r * (deriv D.w r / D.w r)) 2
      (radialHilbertMeasure D) := hq₂.fun_mul (matchingLogDerivative_memLp hD)
  have hsum : MemLp (fun r => q₁ r + q₂ r * (deriv D.w r / D.w r)) 2
      (radialHilbertMeasure D) := hq₁.add hmul
  apply (memLp_congr_ae ?_).mp hsum
  apply (radialHilbertMeasure_ae_iff hD).mpr
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  have hw0 : D.w r ≠ 0 := (hg.2.2.2.2.1 r hr).ne'
  have hr0 : r ≠ 0 := (lt_trans hg.1 hr.1).ne'
  dsimp only [q₁, q₂, matchingJacobiTest]
  rw [matchingJacobi_expansion hD hψ]
  unfold matchingDensity
  field_simp [hw0, hr0]
  <;> ring

/-- This integrability holds for every smooth test, even without a compact
support assumption. The integration interval itself is finite. -/
theorem matchingJacobi_intervalIntegrable {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (U : RadialModeL2 D) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : ℕ) :
    IntervalIntegrable (fun r => U r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r)
      volume D.a D.b := by
  have ht := matchingJacobiTest_memLp hD hψ j
  have hi := (matchingDensity_integrable_iff hD
    (fun r => U r * matchingJacobiTest D j ψ r)).mp ((Lp.memLp U).integrable_mul ht)
  have hi' : Integrable (fun r => U r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r)
      (volume.restrict (radialCore D)) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
      with r hr
    unfold matchingJacobiTest
    field_simp [(matchingDensity_pos hD hr).ne']
    <;> ring
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (matchingProfileGeometry hD).2.1.le).mpr hi'

theorem matchingJacobi_integral_eq_inner {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (U : RadialModeL2 D) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : ℕ) :
    (∫ r in D.a..D.b, U r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
      ⟪U, (matchingJacobiTest_memLp hD hψ j).toLp (matchingJacobiTest D j ψ)⟫_ℝ := by
  calc
    (∫ r in D.a..D.b, U r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
        ∫ r in D.a..D.b, matchingDensity D r * U r * matchingJacobiTest D j ψ r := by
      apply matchingInterval_congr_ae hD
      apply (radialHilbertMeasure_ae_iff hD).mpr
      filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
        with r hr
      unfold matchingJacobiTest
      field_simp [(matchingDensity_pos hD hr).ne']
      <;> ring
    _ = _ := matchingSource_integral_eq_inner hD U (matchingJacobiTest_memLp hD hψ j)

end ContinuousFlexibility.Radial
