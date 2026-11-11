import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The angular period in the physical distributional graph

`RadialTest` permits every smooth test of period `2 * pi`. Consequently its
weak pairing must use the full-period `radialAngularMean`. Pairing those tests
over a half-period introduces an artificial boundary at angles zero and pi.

The constant unknown and the test `sin` exhibit the error already for the
angular second derivative. This audit is independent of any blueprint node.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory

theorem n06_halfPeriod_negative_sin :
    angularMean (fun θ : ℝ => -Real.sin θ) = -(2 / Real.pi) := by
  have hi : (∫ θ in (0 : ℝ)..Real.pi, -Real.sin θ) = -2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => Real.hasDerivAt_cos θ)
      (Real.continuous_sin.neg.intervalIntegrable 0 Real.pi)]
    norm_num
  rw [angularMean, hi]
  ring

theorem n06_fullPeriod_negative_sin :
    radialAngularMean (fun θ : ℝ => -Real.sin θ) = 0 := by
  have hi : (∫ θ in (0 : ℝ)..2 * Real.pi, -Real.sin θ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => Real.hasDerivAt_cos θ)
      (Real.continuous_sin.neg.intervalIntegrable 0 (2 * Real.pi))]
    norm_num
  rw [radialAngularMean, hi, mul_zero]

/-- A permitted full-period test does not give integration by parts on a
half-period, even for a constant, hence half-periodic, unknown. -/
theorem n06_halfPeriod_weak_pairing_counterexample :
    Function.Periodic (fun _ : ℝ => (1 : ℝ)) Real.pi ∧
    Function.Periodic Real.sin (2 * Real.pi) ∧
    angularMean (fun θ : ℝ => (1 : ℝ) * deriv (deriv Real.sin) θ) ≠
      angularMean (fun θ : ℝ => deriv (deriv (fun _ : ℝ => (1 : ℝ))) θ * Real.sin θ) := by
  refine ⟨fun _ => rfl, fun θ => Real.sin_add_two_pi θ, ?_⟩
  have hs : deriv (deriv Real.sin) = fun θ : ℝ => -Real.sin θ := by
    rw [Real.deriv_sin]
    funext θ
    exact Real.deriv_cos θ
  have hc : deriv (deriv (fun _ : ℝ => (1 : ℝ))) = fun _ : ℝ => 0 := by
    simp
  rw [hs, hc]
  simp only [one_mul, zero_mul]
  rw [n06_halfPeriod_negative_sin]
  have hzero : angularMean (fun _ : ℝ => (0 : ℝ)) = 0 := by simp [angularMean]
  rw [hzero]
  exact neg_ne_zero.mpr (div_ne_zero (by norm_num) Real.pi_ne_zero)

/-- The same test satisfies the correct weak identity on the full circle. -/
theorem n06_fullPeriod_weak_pairing_restored :
    radialAngularMean (fun θ : ℝ => (1 : ℝ) * deriv (deriv Real.sin) θ) =
      radialAngularMean
        (fun θ : ℝ => deriv (deriv (fun _ : ℝ => (1 : ℝ))) θ * Real.sin θ) := by
  have hs : deriv (deriv Real.sin) = fun θ : ℝ => -Real.sin θ := by
    rw [Real.deriv_sin]
    funext θ
    exact Real.deriv_cos θ
  have hc : deriv (deriv (fun _ : ℝ => (1 : ℝ))) = fun _ : ℝ => 0 := by simp
  rw [hs, hc]
  simp only [one_mul, zero_mul]
  rw [n06_fullPeriod_negative_sin]
  simp [radialAngularMean]

end ContinuousFlexibility.Statements
