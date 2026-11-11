import ContinuousFlexibility.Radial.CentralModel
import ContinuousFlexibility.Radial.CentralTravelAngle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The physical optical integral of the central model

The integral is taken in the actual radial variable. Its evaluation
uses the proved derivative of the radius and the actual profile
pullback, including the central density-root factor.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

/-- Optical change of variables with its actual positive radial speed. -/
theorem opticalTravel_integral_of_pullback
    {w R v ρ : ℝ → ℝ} {a b : ℝ}
    (hR : ∀ x ∈ uIcc a b, HasDerivAt R (v x) x)
    (hv : ContinuousOn v (uIcc a b))
    (hvpos : ∀ x ∈ uIcc a b, 0 < v x)
    (hdensity : ∀ x ∈ uIcc a b,
      -(deriv w (R x)) / (R x * w (R x)) = ρ x / (v x) ^ 2)
    (hg : ContinuousOn (fun r => sqrt (-(deriv w r) / (r * w r)))
      (R '' uIcc a b)) :
    (∫ r in R a..R b, sqrt (-(deriv w r) / (r * w r))) =
      ∫ x in a..b, sqrt (ρ x) := by
  calc
    _ = ∫ x in a..b, sqrt (-(deriv w (R x)) / (R x * w (R x))) * v x :=
      (intervalIntegral.integral_comp_mul_deriv' hR hv hg).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [hdensity x hx, sqrt_div' _ (sq_nonneg _), sqrt_sq_eq_abs,
        abs_of_pos (hvpos x hx), div_mul_cancel₀ _ (hvpos x hx).ne']

theorem central_opticalDensity_pullback {c : ℝ} (hc : 0 < c) (x : ℝ) :
    -(deriv (centralRadialProfile c) (centralRadius x)) /
        (centralRadius x * centralRadialProfile c (centralRadius x)) =
      (centralOscillatorA - x ^ 2) / (deriv centralRadius x) ^ 2 := by
  have hR : centralRadius x ≠ 0 := (centralRadius_pos x).ne'
  have hs : centralDensityRoot x ≠ 0 := (centralDensityRoot_pos x).ne'
  have hv : deriv centralRadius x ≠ 0 := (deriv_centralRadius_pos x).ne'
  have hd := centralRadialProfile_deriv_scaled c x
  have hdv := congrArg (fun z : ℝ => z * deriv centralRadius x) hd
  rw [centralRadialProfile_pullback]
  field_simp [hc.ne', hR, hs, hv] <;> nlinarith only [hd, hdv]

/-- The central travel angle is computed in physical radius, not merely
asserted for the oscillator coordinate. -/
theorem central_radialTravel_integral {c : ℝ} (hc : 0 < c) :
    (∫ r in centralRadius (-sqrt centralOscillatorA)..centralRadius (sqrt centralOscillatorA),
      sqrt (-(deriv (centralRadialProfile c) r) /
        (r * centralRadialProfile c r))) = Real.pi / (2 * sqrt 2) := by
  have hcontinuity :
      ContinuousOn (fun r => sqrt (-(deriv (centralRadialProfile c) r) /
        (r * centralRadialProfile c r)))
        (centralRadius '' uIcc (-sqrt centralOscillatorA) (sqrt centralOscillatorA)) := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hw := contDiffAt_centralRadialProfile c x
    have hwd : ContinuousAt (deriv (centralRadialProfile c)) (centralRadius x) :=
      (hw.derivWithin (m := ∞) (by simp)).continuousAt
    exact ((hwd.neg.div (continuousAt_id.mul hw.continuousAt)
      (mul_ne_zero (centralRadius_pos x).ne'
        (centralRadialProfile_pos hc (centralRadius_pos x)).ne')).sqrt).continuousWithinAt
  calc
    _ = quadraticTravelIntegral centralOscillatorA :=
      opticalTravel_integral_of_pullback
        (fun x _ => (contDiff_centralRadius.differentiable (by simp) x).hasDerivAt)
        ((contDiff_infty_iff_deriv.mp contDiff_centralRadius).2.continuous.continuousOn)
        (fun x _ => deriv_centralRadius_pos x)
        (fun x _ => central_opticalDensity_pullback hc x) hcontinuity
    _ = Real.pi / (2 * sqrt 2) := by
      rw [central_travel_integral_eq, centralTravelAngle]

end ContinuousFlexibility.Radial
