import ContinuousFlexibility.Radial.CentralSmallDivisor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The actual travel integral of the central model

For the model coefficient `rho(X) = A - X²`, the characteristic travel
integral on its positive component is `∫[-sqrt A,sqrt A] sqrt(A-X²) dX`.
This file computes that integral, specializes to the central oscillator,
and transfers the proved sine lower bound to this actual integral.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Real

/-- The characteristic travel integral of the quadratic central model. -/
def quadraticTravelIntegral (A : ℝ) : ℝ :=
  ∫ X in -Real.sqrt A..Real.sqrt A, Real.sqrt (A - X ^ 2)

/-- The integration bounds are exactly the positive component of the model
coefficient `rho(X) = A - X²`. -/
theorem quadratic_positive_component (A X : ℝ) :
    0 < A - X ^ 2 ↔ X ∈ Set.Ioo (-Real.sqrt A) (Real.sqrt A) := by
  change 0 < A - X ^ 2 ↔ -Real.sqrt A < X ∧ X < Real.sqrt A
  rw [sub_pos, Real.sq_lt]

/-- The change of scale in the integrand, valid also at `A = 0`. -/
theorem quadratic_travel_integrand_scale {A : ℝ} (hA : 0 ≤ A) (X : ℝ) :
    Real.sqrt (A - (Real.sqrt A * X) ^ 2) =
      Real.sqrt A * Real.sqrt (1 - X ^ 2) := by
  rw [mul_pow, Real.sq_sqrt hA]
  rw [show A - A * X ^ 2 = A * (1 - X ^ 2) by ring, Real.sqrt_mul hA]

/-- The actual semicircle integral, proved by the substitution `X = sqrt A * t`.
No travel-angle formula is assumed. -/
theorem quadraticTravelIntegral_eq {A : ℝ} (hA : 0 ≤ A) :
    quadraticTravelIntegral A = Real.pi * A / 2 := by
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (a := (-1 : ℝ)) (b := 1) (fun X => Real.sqrt (A - X ^ 2)) (Real.sqrt A)
  simp only [smul_eq_mul, mul_neg_one, mul_one] at hchange
  have hintegral :
      (∫ X in (-1 : ℝ)..1, Real.sqrt (A - (Real.sqrt A * X) ^ 2)) =
        Real.sqrt A * (Real.pi / 2) := by
    simp only [quadratic_travel_integrand_scale hA,
      intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
  unfold quadraticTravelIntegral
  rw [← hchange, hintegral]
  calc
    _ = Real.pi * Real.sqrt A ^ 2 / 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hA]

theorem quadraticTravelIntegral_pos {A : ℝ} (hA : 0 < A) :
    0 < quadraticTravelIntegral A := by
  rw [quadraticTravelIntegral_eq hA.le]
  positivity

/-- The coefficient `A_c` selected for the central oscillator in Section 4. -/
def centralOscillatorA : ℝ := 1 / Real.sqrt 2

theorem centralOscillatorA_pos : 0 < centralOscillatorA := by
  unfold centralOscillatorA
  positivity

/-- The computed characteristic integral is exactly the central angle whose
small divisors were proved in `CentralSmallDivisor`. -/
theorem central_travel_integral_eq :
    quadraticTravelIntegral centralOscillatorA = centralTravelAngle := by
  rw [quadraticTravelIntegral_eq centralOscillatorA_pos.le]
  unfold centralOscillatorA centralTravelAngle
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hs]

/-- The actual central travel integral has the required characteristic
nonresonance, with the same explicit constant `1/8`. -/
theorem central_travel_integral_small_divisor (k : ℕ) (hk : 1 ≤ k) :
    (1 / 8 : ℝ) / (k : ℝ) ≤
      |Real.sin ((k : ℝ) * quadraticTravelIntegral centralOscillatorA)| := by
  rw [central_travel_integral_eq]
  exact central_sine_small_divisor k hk

theorem exists_central_travel_integral_small_divisor :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → c / (k : ℝ) ≤
      |Real.sin ((k : ℝ) * quadraticTravelIntegral centralOscillatorA)| :=
  ⟨1 / 8, by norm_num, central_travel_integral_small_divisor⟩

end

end ContinuousFlexibility.Radial
