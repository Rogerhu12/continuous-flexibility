import ContinuousFlexibility.Analysis.OneHighCircleFourierSeries
import ContinuousFlexibility.Analysis.OneHighCircleFourierSobolevProduct
import ContinuousFlexibility.Analysis.OneHighConvolutionComplex
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The actual angular multiplication commutator

Only the angular variable is Fourier transformed. The commutator kernel
costs one angular derivative of the coefficient. Its high-order estimate
uses the existing complete circle product estimate through the Fourier
series of the nonnegative majorants, so no radial periodic extension is
assumed and no second product inequality is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

/-- Frequency of the period-`π` operator `Λ = |Dθ| / 2`. -/
def n07aCircleFrequency (n : ℤ) : ℝ := |(n : ℝ)|

def n07aCircleLambda (F : ℤ → ℂ) (n : ℤ) : ℂ :=
  (n07aCircleFrequency n : ℂ) * F n

def n07aCircleCommutator (F G : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∫ k : ℤ, ((n07aCircleFrequency n - n07aCircleFrequency (n - k) : ℝ) : ℂ) *
    F k * G (n - k) ∂Measure.count

theorem n07aCircleFrequency_nonneg (n : ℤ) : 0 ≤ n07aCircleFrequency n := abs_nonneg _

theorem n07aCircleFrequency_difference (n k : ℤ) :
    |n07aCircleFrequency n - n07aCircleFrequency (n - k)| ≤ n07aCircleFrequency k := by
  have h := abs_norm_sub_norm_le (n : ℝ) ((n : ℝ) - (k : ℝ))
  rw [show (n : ℝ) - ((n : ℝ) - (k : ℝ)) = (k : ℝ) by ring] at h
  simpa only [n07aCircleFrequency, Int.cast_sub, Real.norm_eq_abs] using h

theorem n07aCircleLambda_norm (F : ℤ → ℂ) (n : ℤ) :
    ‖n07aCircleLambda F n‖ = n07aCircleFrequency n * ‖F n‖ := by
  rw [n07aCircleLambda, norm_mul, Complex.norm_of_nonneg (n07aCircleFrequency_nonneg n)]

private def n07aCirclePositive (F : ℤ → ℂ) (n : ℤ) : ℂ := (‖F n‖ : ℂ)

private theorem n07aCirclePositive_norm (F : ℤ → ℂ) (n : ℤ) :
    ‖n07aCirclePositive F n‖ = ‖F n‖ := Complex.norm_of_nonneg (norm_nonneg _)

private theorem n07aCirclePositive_memLp {F : ℤ → ℂ} {p : ℝ≥0∞}
    (hF : MemLp F p Measure.count) : MemLp (n07aCirclePositive F) p Measure.count :=
  hF.of_le (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall fun n => (n07aCirclePositive_norm F n).le)

private theorem n07aCirclePositive_eLpNorm (F : ℤ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (n07aCirclePositive F) p Measure.count = eLpNorm F p Measure.count :=
  eLpNorm_congr_norm_ae (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall (n07aCirclePositive_norm F))

private theorem n07aCirclePositive_weighted_eLpNorm (F : ℤ → ℂ) (W : ℤ → ℝ)
    (s : ℝ) (p : ℝ≥0∞) :
    eLpNorm (frequencyWeighted W s (n07aCirclePositive F)) p Measure.count =
      eLpNorm (frequencyWeighted W s F) p Measure.count := by
  apply eLpNorm_congr_norm_ae (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall fun n => by
    rw [frequencyWeighted_apply, frequencyWeighted_apply, norm_smul, norm_smul,
      n07aCirclePositive_norm]

/-- Positive Fourier majorants control the actual absolute-frequency
commutator, with no cancellation or extra regularity assumption on `G`. -/
private theorem n07aCircleCommutator_norm_le {F G : ℤ → ℂ}
    (hF : MemLp (n07aCircleLambda F) 2 Measure.count)
    (hG : MemLp G 2 Measure.count) (n : ℤ) :
    ‖n07aCircleCommutator F G n‖ ≤
      ‖complexConvolution Measure.count
        (n07aCirclePositive (n07aCircleLambda F)) (n07aCirclePositive G) n‖ := by
  have hint : Integrable (fun k : ℤ => ‖n07aCircleLambda F k‖ * ‖G (n - k)‖)
      Measure.count :=
    (ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℝ ℝ) hF.norm hG.norm n).integrable
  have hmajor : ‖n07aCircleCommutator F G n‖ ≤
      ∫ k : ℤ, ‖n07aCircleLambda F k‖ * ‖G (n - k)‖ ∂Measure.count := by
    apply norm_integral_le_of_norm_le hint
    exact Eventually.of_forall fun k => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, n07aCircleLambda_norm]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (n07aCircleFrequency_difference n k) (norm_nonneg _))
        (norm_nonneg _)
  have he : complexConvolution Measure.count
      (n07aCirclePositive (n07aCircleLambda F)) (n07aCirclePositive G) n =
      ((∫ k : ℤ, ‖n07aCircleLambda F k‖ * ‖G (n - k)‖ ∂Measure.count : ℝ) : ℂ) := by
    rw [complexConvolution_apply]
    simp only [n07aCirclePositive, ← Complex.ofReal_mul]
    exact integral_complex_ofReal
  rw [he, Complex.norm_of_nonneg (integral_nonneg fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact hmajor

/-- The kernel is the difference of the two genuine convolution terms
whenever the inputs have the indicated first angular derivatives. -/
theorem n07aCircleCommutator_eq {F G : ℤ → ℂ}
    (hF : MemLp F 2 Measure.count) (hG : MemLp G 2 Measure.count)
    (hΛG : MemLp (n07aCircleLambda G) 2 Measure.count) (n : ℤ) :
    n07aCircleCommutator F G n =
      n07aCircleLambda (complexConvolution Measure.count F G) n -
        complexConvolution Measure.count F (n07aCircleLambda G) n := by
  have hi : Integrable (fun k => F k * G (n - k)) Measure.count :=
    (ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ) hF hG n).integrable
  have hj : Integrable (fun k => F k * n07aCircleLambda G (n - k)) Measure.count :=
    (ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ) hF hΛG n).integrable
  rw [n07aCircleLambda, complexConvolution_apply, complexConvolution_apply,
    ← integral_const_mul, ← integral_sub (hi.const_mul _) hj]
  apply integral_congr_ae
  exact Eventually.of_forall fun k => by
    simp only [n07aCircleLambda, Complex.ofReal_sub]
    ring

variable {P : ℝ} [Fact (0 < P)]

private theorem n07aCirclePositive_convolution_bound (s : ℕ) {A G : ℤ → ℂ}
    (hA : MemLp A 1 Measure.count) (hG : MemLp G 1 Measure.count)
    (hA2 : MemLp A 2 Measure.count) (hG2 : MemLp G 2 Measure.count) :
    eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (complexConvolution Measure.count (n07aCirclePositive A) (n07aCirclePositive G)))
        2 Measure.count ≤
      (2 : ℝ≥0∞) ^ s *
        (eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ) A)
          2 Measure.count * eLpNorm G 1 Measure.count +
        eLpNorm A 1 Measure.count *
          eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ) G)
            2 Measure.count) := by
  let f : C(AddCircle P, ℂ) := circleFourierSeries (n07aCirclePositive A)
  let g : C(AddCircle P, ℂ) := circleFourierSeries (n07aCirclePositive G)
  have ha : Summable (fun n => ‖n07aCirclePositive A n‖) :=
    integrable_count_iff.mp (memLp_one_iff_integrable.mp (n07aCirclePositive_memLp hA))
  have hg : Summable (fun n => ‖n07aCirclePositive G n‖) :=
    integrable_count_iff.mp (memLp_one_iff_integrable.mp (n07aCirclePositive_memLp hG))
  have hfcoef : fourierCoeff f = n07aCirclePositive A :=
    funext (circle_fourierCoeff_series ha)
  have hgcoef : fourierCoeff g = n07aCirclePositive G :=
    funext (circle_fourierCoeff_series hg)
  have hf1 : MemLp (fourierCoeff f) 1 Measure.count := by
    rw [hfcoef]
    exact n07aCirclePositive_memLp hA
  have he : fourierCoeff (f * g) =
      complexConvolution Measure.count (n07aCirclePositive A) (n07aCirclePositive G) := by
    funext n
    have hi : Integrable (fun k => n07aCirclePositive A k * n07aCirclePositive G (n - k))
        Measure.count :=
      (ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ)
        (n07aCirclePositive_memLp hA2) (n07aCirclePositive_memLp hG2) n).integrable
    rw [circle_fourierCoeff_mul_eq_tsum f g hf1 n, hfcoef, hgcoef,
      complexConvolution_apply, integral_countable hi]
    simp only [count_real_singleton, one_smul]
  have h := circle_eLpNorm_weighted_fourierCoeff_mul_le s f g hf1
  rw [he, hfcoef, hgcoef, n07aCirclePositive_weighted_eLpNorm,
    n07aCirclePositive_weighted_eLpNorm, n07aCirclePositive_eLpNorm,
    n07aCirclePositive_eLpNorm] at h
  exact h

/-- The high-order commutator estimate puts exactly one high norm on one
factor and one additional angular derivative on the coefficient. -/
theorem n07aCircleCommutator_eLpNorm_le (s : ℕ) {F G : ℤ → ℂ}
    (hΛF1 : MemLp (n07aCircleLambda F) 1 Measure.count)
    (hΛF2 : MemLp (n07aCircleLambda F) 2 Measure.count)
    (hG1 : MemLp G 1 Measure.count) (hG2 : MemLp G 2 Measure.count) :
    eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (n07aCircleCommutator F G)) 2 Measure.count ≤
      (2 : ℝ≥0∞) ^ s *
        (eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ) (n07aCircleLambda F))
          2 Measure.count * eLpNorm G 1 Measure.count +
        eLpNorm (n07aCircleLambda F) 1 Measure.count *
          eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ) G)
            2 Measure.count) := by
  apply (eLpNorm_mono_ae (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall fun n => ?_)).trans
      (n07aCirclePositive_convolution_bound (P := P) s hΛF1 hG1 hΛF2 hG2)
  rw [frequencyWeighted_apply, frequencyWeighted_apply, norm_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (n07aCircleCommutator_norm_le hΛF2 hG2 n) (norm_nonneg _)

end ContinuousFlexibility.Analysis
