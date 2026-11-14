module

public import ContinuousFlexibility.Radial.R11bFourierTests

/-!
# The actual weak equation of the zero angular channel

The zero channel is the angular mean, without the positive-mode square-root
normalization. Its border contribution vanishes by the cosine mode's zero
mean. The resulting one-dimensional equation uses the same interior tests as
the general weak-divergence regularity lemmas.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_radialAngularMean_const (c : ℝ) :
    radialAngularMean (fun _ : ℝ => c) = c := by
  simp only [radialAngularMean, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp [Real.pi_ne_zero]

theorem r11b_radialTest_radial {D : ReferenceData} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) :
    RadialTest D (fun x : PolarPoint => φ x.1) := by
  have h := r11b_radialTest_separated hφ hφc hφs
    (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)))
    (show Function.Periodic (fun _ : ℝ => (1 : ℝ)) (2 * Real.pi) from fun _ => rfl)
  simpa only [mul_one] using h

theorem r11b_radialPDE_radial (w φ : ℝ → ℝ) (r θ : ℝ) :
    radialPDE w (fun t _ => φ t) r θ = deriv (fun t => w t * deriv φ t) r := by
  simp only [radialPDE, deriv_const', deriv_const, mul_zero, add_zero]

theorem r11b_radialWeakPairing_mean (D : ReferenceData) (u : PolarPoint → ℝ)
    (φ : ℝ → ℝ) :
    radialWeakPairing D u (fun x : PolarPoint => φ x.1) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ)) *
        deriv (fun t => D.w t * deriv φ t) r := by
  unfold radialWeakPairing
  apply intervalIntegral.integral_congr
  intro r _
  change radialAngularMean (fun θ => u (r, θ) *
    radialPDE D.w (fun t _ => φ t) r θ) = _
  simp_rw [r11b_radialPDE_radial]
  exact r11b_radialAngularMean_mul_const (fun θ => u (r, θ))
    (deriv (fun t => D.w t * deriv φ t) r)

theorem r11b_referenceBorder_radial_pairing (D : ReferenceData) (φ : ℝ → ℝ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      referenceColumn D r * cosineMode 2 θ * φ r)) = 0 := by
  have hz (r : ℝ) : radialAngularMean (fun θ =>
      referenceColumn D r * cosineMode 2 θ * φ r) = 0 := by
    rw [r11b_radialAngularMean_mul_const, r11b_radialAngularMean_const_mul,
      r11b_radialAngularMean_eq_angularAverage,
      angularAverage_cosineMode 2 (by decide), mul_zero, zero_mul]
  simp_rw [hz]
  exact intervalIntegral.integral_zero

theorem r11b_referenceGraph_mean_equation {D : ReferenceData} {γ M₀ M₁ : ℝ}
    {U : RadialUnknown} {F : RadialSource} (hUF : ReferenceGraph D γ M₀ M₁ U F)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => U.1 (r, θ)) *
      deriv (fun t => D.w t * deriv φ t) r) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ)) * φ r := by
  have h := hUF.2.2.2 _ (r11b_radialTest_radial hφ hφc hφs)
  rw [r11b_radialWeakPairing_mean] at h
  change _ + U.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
    referenceColumn D r * cosineMode 2 θ * φ r)) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ) * φ r) at h
  rw [r11b_referenceBorder_radial_pairing, mul_zero, add_zero] at h
  simp_rw [r11b_radialAngularMean_mul_const] at h
  exact h

end ContinuousFlexibility.Radial
