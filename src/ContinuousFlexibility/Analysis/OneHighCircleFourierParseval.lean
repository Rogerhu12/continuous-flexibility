import ContinuousFlexibility.Analysis.OneHighCircleFourierBasic

/-!
# Parseval for the physical circle Fourier norm

These wrappers apply the actual normalized-Haar Fourier basis to ordinary
functions. They identify the order-zero frequency Sobolev norm with the
ordinary normalized-Haar `L²` norm, and include the continuous-map form used
for slices of a cylinder.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

/-- Parseval for an arbitrary actual square-integrable circle function. -/
theorem circle_hasSum_sq_fourierCoeff_of_memLp {f : AddCircle P → ℂ}
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)
      (∫ θ, ‖f θ‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  have h := hasSum_sq_fourierCoeff (hf.toLp f)
  have hcoeff := fourierCoeff_congr_ae hf.coeFn_toLp
  have hint : (∫ θ, ‖(hf.toLp f) θ‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∫ θ, ‖f θ‖ ^ 2 ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with θ hθ
    rw [hθ]
  rwa [hcoeff, hint] at h

/-- Parseval in the continuous-map form, without additional hypotheses. -/
theorem circle_hasSum_sq_fourierCoeff (f : C(AddCircle P, ℂ)) :
    HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)
      (∫ θ, ‖f θ‖ ^ 2 ∂AddCircle.haarAddCircle) :=
  circle_hasSum_sq_fourierCoeff_of_memLp
    (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ f)

/-- Square integrability in physical space gives actual square
summability of all integer Fourier modes. -/
theorem circle_fourier_memLp_two_of_memLp {f : AddCircle P → ℂ}
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    MemLp (fourierCoeff f) 2 Measure.count := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_of_countable _).aestronglyMeasurable).mpr
  apply integrable_count_iff.mpr
  refine (circle_hasSum_sq_fourierCoeff_of_memLp hf).summable.congr fun n => ?_
  exact (Real.norm_of_nonneg (sq_nonneg ‖fourierCoeff f n‖)).symm

/-- The integral version of Parseval over the counting frequency measure. -/
theorem circle_integral_sq_fourierCoeff_of_memLp {f : AddCircle P → ℂ}
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    (∫ n : ℤ, ‖fourierCoeff f n‖ ^ 2 ∂Measure.count) =
      ∫ θ, ‖f θ‖ ^ 2 ∂AddCircle.haarAddCircle := by
  have hc := circle_fourier_memLp_two_of_memLp hf
  have hi := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
  calc
    (∫ n : ℤ, ‖fourierCoeff f n‖ ^ 2 ∂Measure.count) =
        ∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2 := by
      simpa only [count_real_singleton, one_smul] using integral_countable hi
    _ = ∫ θ, ‖f θ‖ ^ 2 ∂AddCircle.haarAddCircle :=
      (circle_hasSum_sq_fourierCoeff_of_memLp hf).tsum_eq

/-- The order-zero frequency Sobolev norm is exactly the actual
normalized-Haar `L²` norm. -/
theorem circle_frequencySobolevNorm_zero_eq_l2 {f : AddCircle P → ℂ}
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    frequencySobolevNorm Measure.count (circleFrequencyWeight P) 0 (fourierCoeff f) =
      (eLpNorm f 2 AddCircle.haarAddCircle).toReal := by
  rw [frequencySobolevNorm, frequencyWeighted_zero, toReal_eLpNorm, toReal_eLpNorm]
  rw [lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
      (circle_fourier_memLp_two_of_memLp hf).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable]
  have htwo : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  simp only [htwo, Real.rpow_two, circle_integral_sq_fourierCoeff_of_memLp hf]

end ContinuousFlexibility.Analysis
