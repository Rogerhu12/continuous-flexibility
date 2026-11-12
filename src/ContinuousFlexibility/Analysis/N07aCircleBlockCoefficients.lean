import ContinuousFlexibility.Analysis.N07aCircleCoefficientDecay
import ContinuousFlexibility.Analysis.N07aAngularCosineCoefficients

/-!
# Actual cosine and sine entries of coefficient multiplication

The two frequency shifts are the difference and the sum of the input
and output frequencies. The formula includes the constant mode with its
correct normalization and applies to coefficients of either parity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

def n07aCosineScale (n : ℕ) : ℝ := if n = 0 then 1 else Real.sqrt 2

theorem n07aCosineScale_nonneg (n : ℕ) : 0 ≤ n07aCosineScale n := by
  unfold n07aCosineScale
  split_ifs <;> positivity

theorem n07aCosineScale_le_two (n : ℕ) : n07aCosineScale n ≤ 2 := by
  unfold n07aCosineScale
  split_ifs
  · norm_num
  · exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem n07a_referenceAngularBasis_cos (n : ℕ) (θ : ℝ) :
    referenceAngularBasis n θ = n07aCosineScale n * Real.cos (2 * (n : ℝ) * θ) := by
  cases n with
  | zero => simp only [referenceAngularBasis, n07aCosineScale, ite_true,
      Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, one_mul]
  | succ n => simp only [referenceAngularBasis, cosineMode, n07aCosineScale,
      Nat.succ_ne_zero, ite_false, Nat.cast_mul, Nat.cast_ofNat]

def n07aSineBasis (n : ℕ) (θ : ℝ) : ℝ :=
  n07aCosineScale n * Real.sin (2 * (n : ℝ) * θ)

theorem n07a_referenceAngularBasis_deriv (n : ℕ) (θ : ℝ) :
    deriv (referenceAngularBasis n) θ = -(2 * (n : ℝ)) * n07aSineBasis n θ := by
  have he : referenceAngularBasis n = fun θ =>
      n07aCosineScale n * Real.cos (2 * (n : ℝ) * θ) :=
    funext (n07a_referenceAngularBasis_cos n)
  rw [he]
  have hd := (((hasDerivAt_id θ).const_mul (2 * (n : ℝ))).cos).const_mul (n07aCosineScale n)
  simp only [id_eq] at hd
  convert hd.deriv using 1
  simp only [n07aSineBasis]
  ring

theorem n07aCircleFourierWave_im (n : ℤ) (θ : ℝ) :
    (circleFourierWave n θ).im = Real.sin (2 * (n : ℝ) * θ) := by
  rw [circleFourierWave, fourier_coe_apply]
  have harg : 2 * (Real.pi : ℂ) * Complex.I * n * θ / Real.pi =
      ((2 * (n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [harg, Complex.exp_ofReal_mul_I_im]

theorem n07aCircleFourierCoeff_im {f : ℝ → ℝ} (hf : Continuous f) (n : ℤ) :
    (circleFourierCoeff f n).im =
      -(Real.pi⁻¹ * ∫ θ, f θ * Real.sin (2 * (n : ℝ) * θ) ∂angleMeasure) := by
  have hg : IntervalIntegrable
      (fun θ => circleFourierWave (-n) θ * (f θ : ℂ)) volume 0 Real.pi :=
    ((circleFourierWave_contDiff (-n)).continuous.mul
      (Complex.continuous_ofReal.comp hf)).intervalIntegrable _ _
  rw [n07aCircleFourierCoeff_interval]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have him : (∫ θ in (0 : ℝ)..Real.pi, circleFourierWave (-n) θ * (f θ : ℂ)).im =
      ∫ θ in (0 : ℝ)..Real.pi, (circleFourierWave (-n) θ * (f θ : ℂ)).im :=
    (intervalIntegral.intervalIntegral_im hg).symm
  rw [him]
  have he : (fun θ => (circleFourierWave (-n) θ * (f θ : ℂ)).im) =
      fun θ => -(f θ * Real.sin (2 * (n : ℝ) * θ)) := by
    funext θ
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_add, n07aCircleFourierWave_im, Int.cast_neg, mul_neg, neg_mul, Real.sin_neg]
    ring
  rw [he, intervalIntegral.integral_neg,
    intervalIntegral.integral_of_le Real.pi_pos.le, mul_neg]
  rfl

def n07aCosineAverage (f : ℝ → ℝ) (k : ℤ) : ℝ :=
  Real.pi⁻¹ * ∫ θ, f θ * Real.cos (2 * (k : ℝ) * θ) ∂angleMeasure

def n07aSineAverage (f : ℝ → ℝ) (k : ℤ) : ℝ :=
  Real.pi⁻¹ * ∫ θ, f θ * Real.sin (2 * (k : ℝ) * θ) ∂angleMeasure

theorem n07aCosineAverage_eq_re {f : ℝ → ℝ} (hf : Continuous f) (k : ℤ) :
    n07aCosineAverage f k = (circleFourierCoeff f k).re := by
  rw [n07aCircleFourierCoeff_re ((Complex.continuous_ofReal.comp hf).intervalIntegrable _ _),
    intervalIntegral.integral_of_le Real.pi_pos.le]
  rfl

theorem n07aSineAverage_eq_neg_im {f : ℝ → ℝ} (hf : Continuous f) (k : ℤ) :
    n07aSineAverage f k = -(circleFourierCoeff f k).im := by
  rw [n07aCircleFourierCoeff_im hf, neg_neg]
  rfl

theorem n07aCosineAverage_abs_le {f : ℝ → ℝ} (hf : Continuous f) (k : ℤ) :
    |n07aCosineAverage f k| ≤ ‖circleFourierCoeff f k‖ := by
  rw [n07aCosineAverage_eq_re hf]
  exact Complex.abs_re_le_norm _

theorem n07aSineAverage_abs_le {f : ℝ → ℝ} (hf : Continuous f) (k : ℤ) :
    |n07aSineAverage f k| ≤ ‖circleFourierCoeff f k‖ := by
  rw [n07aSineAverage_eq_neg_im hf, abs_neg]
  exact Complex.abs_im_le_norm _

def n07aCosineMatrixEntry (f : ℝ → ℝ) (l j : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ θ, f θ * referenceAngularBasis j θ * referenceAngularBasis l θ ∂angleMeasure

def n07aSineMatrixEntry (f : ℝ → ℝ) (l j : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ θ, f θ * n07aSineBasis j θ * referenceAngularBasis l θ ∂angleMeasure

theorem n07aCosineMatrixEntry_eq {f : ℝ → ℝ} (hf : Continuous f) (l j : ℕ) :
    n07aCosineMatrixEntry f l j = n07aCosineScale j * n07aCosineScale l / 2 *
      (n07aCosineAverage f ((j : ℤ) - l) + n07aCosineAverage f ((j : ℤ) + l)) := by
  have hi (k : ℤ) : Integrable (fun θ => f θ * Real.cos (2 * (k : ℝ) * θ)) angleMeasure :=
    ((hf.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have he : (fun θ => f θ * referenceAngularBasis j θ * referenceAngularBasis l θ) =
      fun θ => (n07aCosineScale j * n07aCosineScale l / 2) *
        (f θ * Real.cos (2 * (((j : ℤ) - l : ℤ) : ℝ) * θ) +
          f θ * Real.cos (2 * (((j : ℤ) + l : ℤ) : ℝ) * θ)) := by
    funext θ
    rw [n07a_referenceAngularBasis_cos, n07a_referenceAngularBasis_cos]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
    rw [show 2 * ((j : ℝ) - l) * θ = 2 * (j : ℝ) * θ - 2 * (l : ℝ) * θ by ring,
      show 2 * ((j : ℝ) + l) * θ = 2 * (j : ℝ) * θ + 2 * (l : ℝ) * θ by ring,
      ← mul_add, ← Real.two_mul_cos_mul_cos]
    ring
  rw [n07aCosineMatrixEntry, he, integral_const_mul, integral_add (hi _) (hi _)]
  simp only [n07aCosineAverage]
  ring

theorem n07aSineMatrixEntry_eq {f : ℝ → ℝ} (hf : Continuous f) (l j : ℕ) :
    n07aSineMatrixEntry f l j = n07aCosineScale j * n07aCosineScale l / 2 *
      (n07aSineAverage f ((j : ℤ) - l) + n07aSineAverage f ((j : ℤ) + l)) := by
  have hi (k : ℤ) : Integrable (fun θ => f θ * Real.sin (2 * (k : ℝ) * θ)) angleMeasure :=
    ((hf.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have he : (fun θ => f θ * n07aSineBasis j θ * referenceAngularBasis l θ) =
      fun θ => (n07aCosineScale j * n07aCosineScale l / 2) *
        (f θ * Real.sin (2 * (((j : ℤ) - l : ℤ) : ℝ) * θ) +
          f θ * Real.sin (2 * (((j : ℤ) + l : ℤ) : ℝ) * θ)) := by
    funext θ
    rw [n07a_referenceAngularBasis_cos]
    simp only [n07aSineBasis, Int.cast_sub, Int.cast_add, Int.cast_natCast]
    rw [show 2 * ((j : ℝ) - l) * θ = 2 * (j : ℝ) * θ - 2 * (l : ℝ) * θ by ring,
      show 2 * ((j : ℝ) + l) * θ = 2 * (j : ℝ) * θ + 2 * (l : ℝ) * θ by ring,
      ← mul_add, ← Real.two_mul_sin_mul_cos]
    ring
  rw [n07aSineMatrixEntry, he, integral_const_mul, integral_add (hi _) (hi _)]
  simp only [n07aSineAverage]
  ring

end ContinuousFlexibility.Analysis
