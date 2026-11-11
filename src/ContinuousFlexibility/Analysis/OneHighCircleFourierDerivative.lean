import ContinuousFlexibility.Analysis.OneHighCircleFourierBasic

/-!
# Derivatives of actual circle Fourier coefficients

Integration by parts on a full period gives the physical multiplier `iω`.
The argument includes the zero mode, where the derivative coefficient
vanishes because the endpoint values agree.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

/-- The actual derivative of a lifted circle function multiplies every
Fourier coefficient by its physical frequency times `i`. -/
theorem circle_fourierCoeff_of_hasDerivAt (f df : C(AddCircle P, ℂ))
    (hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f (y : AddCircle P)) (df (x : AddCircle P)) x)
    (n : ℤ) :
    fourierCoeff df n =
      (Complex.I * (circlePhysicalFrequency P n : ℂ)) * fourierCoeff f n := by
  have ha : Continuous (fun x : ℝ => fourier (-n) (x : AddCircle P)) :=
    (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' P)
  have hf : Continuous (fun x : ℝ => f (x : AddCircle P)) :=
    f.continuous.comp (AddCircle.continuous_mk' P)
  have hdf : Continuous (fun x : ℝ => df (x : AddCircle P)) :=
    df.continuous.comp (AddCircle.continuous_mk' P)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := P) ha.continuousOn hf.continuousOn
    (fun x _ => hasDerivAt_fourier_neg P n x)
    (fun x _ => hderiv x)
    ((continuous_const.mul ha).intervalIntegrable 0 P)
    (hdf.intervalIntegrable 0 P)
  have hperiod : (P : AddCircle P) = ((0 : ℝ) : AddCircle P) := by
    rw [AddCircle.coe_period, AddCircle.coe_zero]
  rw [hperiod, sub_self, zero_sub] at hi
  simp_rw [mul_assoc] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  rw [fourierCoeff_eq_intervalIntegral df n 0,
    fourierCoeff_eq_intervalIntegral f n 0]
  simp only [zero_add, smul_eq_mul, Complex.real_smul]
  rw [hi]
  simp only [circlePhysicalFrequency, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_intCast]
  norm_num <;> ring

/-- Successive actual derivatives give the expected physical multiplier
at every order. The premise identifies successive derivatives, rather
than assuming any estimate on their Fourier coefficients. -/
theorem circle_fourierCoeff_iterated_derivatives (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (k : ℕ) (n : ℤ) :
    fourierCoeff (f k) n =
      (Complex.I * (circlePhysicalFrequency P n : ℂ)) ^ k * fourierCoeff (f 0) n := by
  induction k with
  | zero => simp only [pow_zero, one_mul]
  | succ k ih =>
      rw [circle_fourierCoeff_of_hasDerivAt (f k) (f (k + 1)) (hderiv k), ih,
        pow_succ]
      ring

end ContinuousFlexibility.Analysis
