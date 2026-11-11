import ContinuousFlexibility.Analysis.OneHighFrequencyEmbedding
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The mixed frequency measure of a cylinder

The radial frequency is real and the angular frequency is an integer. The
two physical frequency scales are explicit: the ordinary Fourier convention
uses `a = 2*pi`, and a circle of period `P` uses `q = 2*pi/P`.

The square of the inverse order-two weight is dominated by a product of
one-dimensional integrable functions. This is the dimension-two part of the
Fourier embedding estimate, with no restriction on the frequency support.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal

/-- Lebesgue measure in the radial frequency and counting measure in the
angular frequency. -/
def cylinderFrequencyMeasure : Measure (ℝ × ℤ) := volume.prod Measure.count

/-- The physical Bessel weight on the mixed cylinder frequencies. -/
def cylinderFrequencyWeight (a q : ℝ) (ζ : ℝ × ℤ) : ℝ :=
  Real.sqrt (1 + (a * ζ.1) ^ 2 + (q * (ζ.2 : ℝ)) ^ 2)

@[simp] theorem cylinderFrequencyWeight_apply (a q : ℝ) (ζ : ℝ × ℤ) :
    cylinderFrequencyWeight a q ζ =
      Real.sqrt (1 + (a * ζ.1) ^ 2 + (q * (ζ.2 : ℝ)) ^ 2) := rfl

theorem cylinderFrequencyWeight_pos (a q : ℝ) (ζ : ℝ × ℤ) :
    0 < cylinderFrequencyWeight a q ζ := by
  rw [cylinderFrequencyWeight_apply]
  exact Real.sqrt_pos.mpr (by positivity)

theorem continuous_cylinderFrequencyWeight (a q : ℝ) :
    Continuous (cylinderFrequencyWeight a q) := by
  have hc : Continuous (fun ζ : ℝ × ℤ =>
      1 + (a * ζ.1) ^ 2 + (q * (ζ.2 : ℝ)) ^ 2) := by fun_prop
  exact Real.continuous_sqrt.comp hc

theorem cylinderFrequencyWeight_neg_two (a q : ℝ) (ζ : ℝ × ℤ) :
    cylinderFrequencyWeight a q ζ ^ (-2 : ℝ) =
      (1 + (a * ζ.1) ^ 2 + (q * (ζ.2 : ℝ)) ^ 2)⁻¹ := by
  rw [Real.rpow_neg (cylinderFrequencyWeight_pos a q ζ).le,
    Real.rpow_two, cylinderFrequencyWeight_apply, Real.sq_sqrt (by positivity)]

private theorem mixed_inverse_square_le (x y : ℝ) :
    ((1 + x ^ 2 + y ^ 2)⁻¹) ^ 2 ≤ (1 + x ^ 2)⁻¹ * (1 + y ^ 2)⁻¹ := by
  have hden : (1 + x ^ 2) * (1 + y ^ 2) ≤ (1 + x ^ 2 + y ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  rw [← inv_pow, ← mul_inv_rev]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hden

/-- The cylinder inverse weight is in `L²` once the one-dimensional
angular inverse weight is integrable. The radial integrability is proved
here from the actual improper integral. -/
theorem cylinder_inverse_weight_memLp_of_count_integrable {a q : ℝ} (ha : a ≠ 0)
    (hq : Integrable (fun n : ℤ => (1 + (q * (n : ℝ)) ^ 2)⁻¹) Measure.count) :
    MemLp (fun ζ => cylinderFrequencyWeight a q ζ ^ (-2 : ℝ)) 2
      cylinderFrequencyMeasure := by
  have hc : Continuous (fun ζ => cylinderFrequencyWeight a q ζ ^ (-2 : ℝ)) :=
    (continuous_cylinderFrequencyWeight a q).rpow_const
      (fun ζ => Or.inl (cylinderFrequencyWeight_pos a q ζ).ne')
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  apply ((Real.integrable_inv_one_add_mul_sq ha).mul_prod hq).mono'
    (hc.pow 2).aestronglyMeasurable
  filter_upwards [] with ζ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), cylinderFrequencyWeight_neg_two]
  exact mixed_inverse_square_le (a * ζ.1) (q * (ζ.2 : ℝ))

/-- The actual mixed-frequency Cauchy--Schwarz estimate at order two.
The angular summability is the sole remaining input from the circle weight. -/
theorem cylinder_frequencyL1_le_H2_of_count_integrable {a q : ℝ} (ha : a ≠ 0)
    (hq : Integrable (fun n : ℤ => (1 + (q * (n : ℝ)) ^ 2)⁻¹) Measure.count)
    {f : ℝ × ℤ → ℂ}
    (hf : MemLp (frequencyWeighted (cylinderFrequencyWeight a q) 2 f) 2
      cylinderFrequencyMeasure) :
    frequencyL1Norm cylinderFrequencyMeasure f ≤
      (eLpNorm (fun ζ => cylinderFrequencyWeight a q ζ ^ (-2 : ℝ)) 2
        cylinderFrequencyMeasure).toReal *
      frequencySobolevNorm cylinderFrequencyMeasure (cylinderFrequencyWeight a q) 2 f :=
  frequencyL1Norm_le_inverse_weight_mul
    (Filter.Eventually.of_forall (cylinderFrequencyWeight_pos a q))
    (cylinder_inverse_weight_memLp_of_count_integrable ha hq) hf

end ContinuousFlexibility.Analysis
