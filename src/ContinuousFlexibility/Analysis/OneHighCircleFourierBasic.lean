module

public import ContinuousFlexibility.Analysis.OneHighCircleFourierWeights
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The physical Fourier norms on a circle

We use the actual Fourier coefficients on `AddCircle P` for normalized Haar
measure. The integer mode `n` has physical frequency `2 * π * n / P`.
The Sobolev and Fourier `L¹` norms are the frequency norms already shared with
the cylinder theory. Pointwise estimates are stated for the continuous
representative, with actual integrability hypotheses on its coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

/-- Physical frequency on the circle of period `P`. -/
def circlePhysicalFrequency (P : ℝ) (n : ℤ) : ℝ :=
  (2 * Real.pi / P) * (n : ℝ)

/-- The physical Bessel weight on circle frequencies. -/
def circleFrequencyWeight (P : ℝ) (n : ℤ) : ℝ :=
  Real.sqrt (1 + circlePhysicalFrequency P n ^ 2)

theorem circleFrequencyWeight_pos (P : ℝ) (n : ℤ) :
    0 < circleFrequencyWeight P n := by
  exact Real.sqrt_pos.mpr (by positivity)

theorem circlePhysicalFrequencyScale_pos (P : ℝ) [hP : Fact (0 < P)] :
    0 < 2 * Real.pi / P :=
  div_pos (mul_pos (by norm_num) Real.pi_pos) hP.out

/-- Counting-measure `L¹` is exactly the absolute Fourier sum. -/
theorem circleFrequencyL1Norm_eq_tsum {a : ℤ → ℂ}
    (ha : MemLp a 1 Measure.count) :
    frequencyL1Norm Measure.count a = ∑' n : ℤ, ‖a n‖ := by
  rw [frequencyL1Norm, toReal_eLpNorm,
    lpNorm_one_eq_integral_norm ha.aestronglyMeasurable,
    integral_countable (memLp_one_iff_integrable.mp ha).norm]
  simp only [count_real_singleton, one_smul]

variable {P : ℝ} [Fact (0 < P)]

/-- Fourier inversion for summable coefficients gives the pointwise bound
with constant one for normalized Haar measure. -/
theorem circle_norm_apply_le_fourierL1Norm (f : C(AddCircle P, ℂ))
    (hf : MemLp (fourierCoeff f) 1 Measure.count) (x : AddCircle P) :
    ‖f x‖ ≤ frequencyL1Norm Measure.count (fourierCoeff f) := by
  rw [circleFrequencyL1Norm_eq_tsum hf]
  have hs : Summable (fun n : ℤ => ‖fourierCoeff f n‖) :=
    integrable_count_iff.mp (memLp_one_iff_integrable.mp hf)
  apply (has_pointwise_sum_fourier_series_of_summable hs.of_norm x).norm_le_of_bounded
    hs.hasSum
  intro n
  simp only [norm_smul, fourier_apply, Circle.norm_coe, mul_one, le_refl]

/-- The ordinary supremum norm is bounded by the absolute Fourier sum. -/
theorem circle_supNorm_le_fourierL1Norm (f : C(AddCircle P, ℂ))
    (hf : MemLp (fourierCoeff f) 1 Measure.count) :
    ‖f‖ ≤ frequencyL1Norm Measure.count (fourierCoeff f) := by
  exact (f.norm_le (frequencyL1Norm_nonneg _ _)).mpr
    (circle_norm_apply_le_fourierL1Norm f hf)

/-- Finiteness of `H¹` implies absolute summability of the actual Fourier
coefficients on every positive-period circle. -/
theorem circle_fourier_memLp_one_of_h1 {f : AddCircle P → ℂ}
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) 1 (fourierCoeff f))
      2 Measure.count) :
    MemLp (fourierCoeff f) 1 Measure.count := by
  apply frequency_memLp_one_of_inverse_weight
    (Eventually.of_forall (circleFrequencyWeight_pos P)) ?_ hf
  simpa only [circleFrequencyWeight, circlePhysicalFrequency] using
    memLp_circleInverseWeight (circlePhysicalFrequencyScale_pos P)

/-- The circle Fourier `L¹` norm is bounded by `H¹`, with the finite
inverse-weight `L²` norm as an explicit constant depending only on `P`. -/
theorem circle_fourierL1Norm_le_h1 {f : AddCircle P → ℂ}
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) 1 (fourierCoeff f))
      2 Measure.count) :
    frequencyL1Norm Measure.count (fourierCoeff f) ≤
      (eLpNorm (fun n : ℤ => circleFrequencyWeight P n ^ (-1 : ℝ))
        2 Measure.count).toReal *
      frequencySobolevNorm Measure.count (circleFrequencyWeight P) 1 (fourierCoeff f) := by
  apply frequencyL1Norm_le_inverse_weight_mul
    (Eventually.of_forall (circleFrequencyWeight_pos P)) ?_ hf
  simpa only [circleFrequencyWeight, circlePhysicalFrequency] using
    memLp_circleInverseWeight (circlePhysicalFrequencyScale_pos P)

/-- The continuous representative is pointwise bounded by its actual
physical `H¹` norm. -/
theorem circle_norm_apply_le_h1 (f : C(AddCircle P, ℂ))
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) 1 (fourierCoeff f))
      2 Measure.count) (x : AddCircle P) :
    ‖f x‖ ≤ (eLpNorm (fun n : ℤ => circleFrequencyWeight P n ^ (-1 : ℝ))
      2 Measure.count).toReal *
      frequencySobolevNorm Measure.count (circleFrequencyWeight P) 1 (fourierCoeff f) :=
  (circle_norm_apply_le_fourierL1Norm f (circle_fourier_memLp_one_of_h1 hf) x).trans
    (circle_fourierL1Norm_le_h1 hf)

end ContinuousFlexibility.Analysis
