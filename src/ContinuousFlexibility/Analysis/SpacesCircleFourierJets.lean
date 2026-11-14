module

public import ContinuousFlexibility.Analysis.SpacesCircleFourier

/-!
# Angular Fourier symbols of the actual circle jets

Differentiation has symbol `2 I n`, consistently with period `π`.
The coefficient identity is proved from integration by parts for smooth
periodic functions and then iterated through all derivative orders.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff

private instance circleFourierJets_period_pos : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem circleFourierWave_periodic (n : ℤ) :
    Function.Periodic (circleFourierWave n) Real.pi := by
  intro θ
  unfold circleFourierWave
  rw [AddCircle.coe_add_period]

theorem circleFourierWave_contDiff (n : ℤ) : ContDiff ℝ ∞ (circleFourierWave n) := by
  unfold circleFourierWave
  simp_rw [fourier_coe_apply]
  exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const (Real.pi : ℂ)).cexp

theorem circleFourierWave_norm (n : ℤ) (θ : ℝ) : ‖circleFourierWave n θ‖ = 1 := by
  simp only [circleFourierWave, fourier_apply, Circle.norm_coe]

theorem circleFourierWave_hasDerivAt (n : ℤ) (θ : ℝ) :
    HasDerivAt (circleFourierWave n)
      ((2 * Complex.I * (n : ℂ)) * circleFourierWave n θ) θ := by
  unfold circleFourierWave
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcoef : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (Real.pi : ℂ)) =
      2 * Complex.I * (n : ℂ) := by
    field_simp
  simpa only [hcoef] using hasDerivAt_fourier Real.pi n θ

private theorem complex_hasDerivAt_of_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    HasDerivAt (fun t => (f t : ℂ)) ((deriv f x : ℝ) : ℂ) x :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
    (hf.differentiable (by simp) x).hasDerivAt

/-- The exact Fourier differentiation formula, including the zero mode. -/
theorem circleFourierCoeff_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (n : ℤ) :
    circleFourierCoeff (deriv f) n =
      (2 * Complex.I * (n : ℂ)) * circleFourierCoeff f n := by
  have hperiod : (f Real.pi : ℂ) = (f 0 : ℂ) :=
    congrArg (fun x : ℝ => (x : ℂ)) (by simpa only [zero_add] using hp 0)
  have hder := complex_hasDerivAt_of_smooth hf
  have hint : IntervalIntegrable (fun x => ((deriv f x : ℝ) : ℂ)) volume 0 Real.pi :=
    (Complex.continuous_ofReal.comp (contDiff_infty_iff_deriv.mp hf).2.continuous).intervalIntegrable _ _
  by_cases hn : n = 0
  · subst n
    have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hder x) hint
    rw [hperiod, sub_self] at hInt
    have hIntAngle : (∫ x, ((deriv f x : ℝ) : ℂ) ∂angleMeasure) = 0 := by
      simpa only [intervalIntegral.integral_of_le Real.pi_pos.le, angleMeasure] using hInt
    rw [circleFourierCoeff_integral]
    simp only [neg_zero, circleFourierWave, fourier_zero, one_mul, hIntAngle,
      Int.cast_zero, mul_zero, zero_mul]
  · have h := fourierCoeffOn_of_hasDerivAt Real.pi_pos hn (fun x _ => hder x) hint
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnc : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    simp only [hperiod, sub_self, mul_zero, zero_sub, sub_zero, Complex.ofReal_zero] at h
    change circleFourierCoeff f n =
      1 / (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        (-((Real.pi : ℂ) * circleFourierCoeff (deriv f) n)) at h
    field_simp [hπ, hnc, Complex.I_ne_zero] at h
    linear_combination -h

theorem circleFourier_contDiff_iteratedDeriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (b : ℕ) : ContDiff ℝ ∞ (iteratedDeriv b f) := by
  induction b with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ b ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

theorem circleFourier_periodic_iteratedDeriv {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (b : ℕ) :
    Function.Periodic (iteratedDeriv b f) Real.pi := by
  intro x
  have hshift : (fun t : ℝ => f (t + Real.pi)) = f := funext hp
  have h := congrFun (iteratedDeriv_comp_add_const b f Real.pi) x
  rw [hshift] at h
  exact h.symm

/-- Every angular derivative corresponds to the prescribed power of the
Fourier frequency, with no loss of derivative order. -/
theorem circleFourierCoeff_iteratedDeriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (b : ℕ) (n : ℤ) :
    circleFourierCoeff (iteratedDeriv b f) n =
      (2 * Complex.I * (n : ℂ)) ^ b * circleFourierCoeff f n := by
  induction b with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ b ih =>
    rw [iteratedDeriv_succ,
      circleFourierCoeff_deriv (circleFourier_contDiff_iteratedDeriv hf b)
        (circleFourier_periodic_iteratedDeriv hp b), ih, pow_succ]
    ring

theorem circleFourierCoeff_iteratedDeriv_norm {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (b : ℕ) (n : ℤ) :
    ‖circleFourierCoeff (iteratedDeriv b f) n‖ =
      (2 * |(n : ℝ)|) ^ b * ‖circleFourierCoeff f n‖ := by
  rw [circleFourierCoeff_iteratedDeriv hf hp b n, norm_mul, norm_pow]
  simp only [norm_mul, Complex.norm_two, Complex.norm_I, Complex.norm_intCast, mul_one]

end ContinuousFlexibility.Statements
