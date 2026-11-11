import ContinuousFlexibility.Analysis.OneHighCircleFourierDerivative
import ContinuousFlexibility.Analysis.OneHighCircleFourierParseval
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Physical weights and actual circle derivative jets

The frequency is `2 * π * n / P` throughout. These elementary bounds and
coefficient identities connect a family of actual successive derivatives to
the Bessel Sobolev norm, without changing its representation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

theorem circleFrequencyWeight_one_le (P : ℝ) (n : ℤ) :
    1 ≤ circleFrequencyWeight P n := by
  have hs : circleFrequencyWeight P n ^ 2 =
      1 + circlePhysicalFrequency P n ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hp := circleFrequencyWeight_pos P n
  nlinarith [sq_nonneg (circlePhysicalFrequency P n)]

theorem abs_circlePhysicalFrequency_le_weight (P : ℝ) (n : ℤ) :
    |circlePhysicalFrequency P n| ≤ circleFrequencyWeight P n := by
  have hs : circleFrequencyWeight P n ^ 2 =
      1 + circlePhysicalFrequency P n ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hp := circleFrequencyWeight_pos P n
  have ha := abs_nonneg (circlePhysicalFrequency P n)
  nlinarith [sq_abs (circlePhysicalFrequency P n)]

theorem circleFrequencyWeight_le_one_add_abs (P : ℝ) (n : ℤ) :
    circleFrequencyWeight P n ≤ 1 + |circlePhysicalFrequency P n| := by
  have hs : circleFrequencyWeight P n ^ 2 =
      1 + circlePhysicalFrequency P n ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hp := circleFrequencyWeight_pos P n
  have ha := abs_nonneg (circlePhysicalFrequency P n)
  nlinarith [sq_abs (circlePhysicalFrequency P n)]

/-- A finite-order Bessel weight is bounded by the two endpoint derivative
weights. The constant does not depend on the circle period. -/
theorem circleFrequencyWeight_nat_pow_le (P : ℝ) (n : ℤ) (s : ℕ) :
    circleFrequencyWeight P n ^ s ≤
      (2 : ℝ) ^ s * (1 + |circlePhysicalFrequency P n| ^ s) := by
  have hW := circleFrequencyWeight_pos P n
  have hupper := circleFrequencyWeight_le_one_add_abs P n
  by_cases hω : |circlePhysicalFrequency P n| ≤ 1
  · have hW2 : circleFrequencyWeight P n ≤ 2 := by linarith
    calc
      circleFrequencyWeight P n ^ s ≤ (2 : ℝ) ^ s :=
        pow_le_pow_left₀ hW.le hW2 s
      _ ≤ (2 : ℝ) ^ s * (1 + |circlePhysicalFrequency P n| ^ s) := by
        have hp : 0 ≤ |circlePhysicalFrequency P n| ^ s := by positivity
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s]
  · have hω1 : 1 ≤ |circlePhysicalFrequency P n| := le_of_lt (lt_of_not_ge hω)
    have hW2 : circleFrequencyWeight P n ≤ 2 * |circlePhysicalFrequency P n| := by
      linarith
    calc
      circleFrequencyWeight P n ^ s ≤ (2 * |circlePhysicalFrequency P n|) ^ s :=
        pow_le_pow_left₀ hW.le hW2 s
      _ = (2 : ℝ) ^ s * |circlePhysicalFrequency P n| ^ s := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ s * (1 + |circlePhysicalFrequency P n| ^ s) := by
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s]

theorem circle_norm_frequencyWeighted_nat (P : ℝ) (s : ℕ) (a : ℤ → ℂ) (n : ℤ) :
    ‖frequencyWeighted (circleFrequencyWeight P) (s : ℝ) a n‖ =
      circleFrequencyWeight P n ^ s * ‖a n‖ := by
  rw [frequencyWeighted_apply, norm_smul, Real.rpow_natCast,
    Real.norm_of_nonneg (pow_nonneg (circleFrequencyWeight_pos P n).le s)]

theorem circle_enorm_frequencyWeighted_nat (P : ℝ) (s : ℕ) (a : ℤ → ℂ) (n : ℤ) :
    ‖frequencyWeighted (circleFrequencyWeight P) (s : ℝ) a n‖ₑ =
      ENNReal.ofReal (circleFrequencyWeight P n) ^ s * ‖a n‖ₑ := by
  rw [frequencyWeighted_enorm (circleFrequencyWeight_pos P n), ENNReal.rpow_natCast]

/-- The positive weighted coefficient norm used by convolution is exactly
the norm of the complex weighted Fourier data. -/
theorem circle_eLpNorm_weighted_enorm (P : ℝ) (s : ℕ) (a : ℤ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun n => ENNReal.ofReal (circleFrequencyWeight P n) ^ s * ‖a n‖ₑ)
        p Measure.count =
      eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ) a) p Measure.count := by
  have heq : (fun n => ENNReal.ofReal (circleFrequencyWeight P n) ^ s * ‖a n‖ₑ) =
      fun n => ‖frequencyWeighted (circleFrequencyWeight P) (s : ℝ) a n‖ₑ := by
    funext n
    exact (circle_enorm_frequencyWeighted_nat P s a n).symm
  rw [heq]
  exact eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable

variable {P : ℝ} [Fact (0 < P)]

/-- The physical circle Sobolev norm, using the same frequency norm as the
cylinder and interpolation lemmas. -/
abbrev circleSobolevNorm (s : ℝ) (f : AddCircle P → ℂ) : ℝ :=
  frequencySobolevNorm Measure.count (circleFrequencyWeight P) s (fourierCoeff f)

theorem circle_norm_fourierCoeff_iterated_derivatives
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (k : ℕ) (n : ℤ) :
    ‖fourierCoeff (f k) n‖ =
      |circlePhysicalFrequency P n| ^ k * ‖fourierCoeff (f 0) n‖ := by
  rw [circle_fourierCoeff_iterated_derivatives f hderiv k n]
  simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, one_mul]

theorem circle_enorm_fourierCoeff_iterated_derivatives
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (k : ℕ) (n : ℤ) :
    ‖fourierCoeff (f k) n‖ₑ =
      ENNReal.ofReal |circlePhysicalFrequency P n| ^ k * ‖fourierCoeff (f 0) n‖ₑ := by
  rw [← ofReal_norm, circle_norm_fourierCoeff_iterated_derivatives f hderiv k n,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (abs_nonneg _), ofReal_norm]

theorem circle_norm_fourierCoeff_derivative_le_weight
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    {k s : ℕ} (hks : k ≤ s) (n : ℤ) :
    ‖fourierCoeff (f k) n‖ ≤
      circleFrequencyWeight P n ^ s * ‖fourierCoeff (f 0) n‖ := by
  rw [circle_norm_fourierCoeff_iterated_derivatives f hderiv k n]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (pow_le_pow_left₀ (abs_nonneg _) (abs_circlePhysicalFrequency_le_weight P n) k).trans
    (pow_le_pow_right₀ (circleFrequencyWeight_one_le P n) hks)

theorem circle_enorm_fourierCoeff_derivative_le_weight
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    {k s : ℕ} (hks : k ≤ s) (n : ℤ) :
    ‖fourierCoeff (f k) n‖ₑ ≤
      ENNReal.ofReal (circleFrequencyWeight P n) ^ s * ‖fourierCoeff (f 0) n‖ₑ := by
  have h := ENNReal.ofReal_le_ofReal
    (circle_norm_fourierCoeff_derivative_le_weight f hderiv hks n)
  simpa only [ENNReal.ofReal_mul (pow_nonneg (circleFrequencyWeight_pos P n).le s),
    ENNReal.ofReal_pow (circleFrequencyWeight_pos P n).le, ofReal_norm] using h

/-- Parseval expressed directly as equality of real-valued `L²` norms. -/
theorem circle_fourier_l2_toReal (f : C(AddCircle P, ℂ)) :
    (eLpNorm (fourierCoeff f) 2 Measure.count).toReal =
      (eLpNorm f 2 AddCircle.haarAddCircle).toReal := by
  simpa only [frequencySobolevNorm, frequencyWeighted_zero] using
    circle_frequencySobolevNorm_zero_eq_l2
      (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ f)

end ContinuousFlexibility.Analysis
