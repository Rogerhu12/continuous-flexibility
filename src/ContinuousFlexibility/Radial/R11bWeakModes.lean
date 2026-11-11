import ContinuousFlexibility.Radial.R11bFourierTests

/-!
# The scalar weak equations obtained from the actual reference graph

Testing the two-dimensional equation against a compact radial function times
a cosine produces the ordinary radial Jacobi equation. The border occurs only
in mode two. Testing an angular weak derivative against a sine gives the
corresponding first-order coefficient identity, with its actual sign.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_radialWeakPairing_cosine {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (u : PolarPoint → ℝ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : ℕ) :
    radialWeakPairing D u (fun x : PolarPoint => φ x.1 * cosineMode j x.2) =
      ∫ r in D.a..D.b,
        referenceMode u j r * radialJacobi ((j : ℝ) ^ 2) D.w φ r := by
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hflux : ContDiff ℝ ∞ (fun r => D.w r * deriv φ r) := hgeom.2.2.1.1.mul hφd
  unfold radialWeakPairing
  apply intervalIntegral.integral_congr
  intro r _
  change radialAngularMean (fun θ => u (r, θ) *
    radialPDE D.w (fun t θ => φ t * cosineMode j θ) r θ) = _
  have hPDE (θ : ℝ) :
      radialPDE D.w (fun t θ => φ t * cosineMode j θ) r θ =
        radialJacobi ((j : ℝ) ^ 2) D.w φ r * cosineMode j θ :=
    radialPDE_cosine_lift j
      (Eventually.of_forall fun t => hφ.differentiable (by simp) t)
      (hflux.differentiable (by simp) r)
  simp_rw [hPDE]
  exact r11b_radialAngularMean_lift_pairing (fun θ => u (r, θ)) (cosineMode j)
    (radialJacobi ((j : ℝ) ^ 2) D.w φ r)

theorem r11b_referenceBorder_cosine_pairing (D : ReferenceData) (φ : ℝ → ℝ)
    (j : ℕ) (hj : 0 < j) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      referenceColumn D r * cosineMode 2 θ * (φ r * cosineMode j θ))) =
      (if j = 2 then 1 else 0) *
        ∫ r in D.a..D.b, referenceColumn D r * φ r := by
  have horth : radialAngularMean (fun θ => cosineMode 2 θ * cosineMode j θ) =
      if j = 2 then 1 else 0 := by
    rw [r11b_radialAngularMean_eq_angularAverage]
    change angularPairing (cosineMode 2) (cosineMode j) = _
    simpa only [eq_comm] using angularPairing_cosineMode 2 j (by decide) hj
  have hpoint (r : ℝ) :
      radialAngularMean (fun θ =>
        referenceColumn D r * cosineMode 2 θ * (φ r * cosineMode j θ)) =
        (if j = 2 then 1 else 0) * (referenceColumn D r * φ r) := by
    have heq : (fun θ => referenceColumn D r * cosineMode 2 θ *
        (φ r * cosineMode j θ)) =
        (fun θ => (referenceColumn D r * φ r) * (cosineMode 2 θ * cosineMode j θ)) := by
      funext θ
      ring
    rw [heq, r11b_radialAngularMean_const_mul, horth, mul_comm]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]

/-- This is the scalar distributional equation for every strict interior
radial test. Boundary-touching tests are handled by a separate approximation. -/
theorem r11b_referenceGraph_mode_equation {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {γ M₀ M₁ : ℝ}
    {U : RadialUnknown} {F : RadialSource} (hUF : ReferenceGraph D γ M₀ M₁ U F)
    (j : ℕ) (hj : 0 < j) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) :
    (∫ r in D.a..D.b,
      referenceMode U.1 j r * radialJacobi ((j : ℝ) ^ 2) D.w φ r) +
        (if j = 2 then U.2 else 0) *
          (∫ r in D.a..D.b, referenceColumn D r * φ r) =
      ∫ r in D.a..D.b, referenceMode F.1 j r * φ r := by
  have h := hUF.2.2.2 _ (r11b_radialTest_cosine hφ hφc hφs j)
  rw [r11b_radialWeakPairing_cosine hgeom U.1 hφ j] at h
  change _ + U.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
    referenceColumn D r * cosineMode 2 θ * (φ r * cosineMode j θ))) =
    ∫ r in D.a..D.b, radialAngularMean (fun θ =>
      F.1 (r, θ) * (φ r * cosineMode j θ)) at h
  rw [r11b_referenceBorder_cosine_pairing D φ j hj] at h
  have hright :
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        F.1 (r, θ) * (φ r * cosineMode j θ))) =
        ∫ r in D.a..D.b, referenceMode F.1 j r * φ r := by
    apply intervalIntegral.integral_congr
    intro r _
    exact r11b_radialAngularMean_lift_pairing (fun θ => F.1 (r, θ)) (cosineMode j) (φ r)
  rw [hright] at h
  by_cases hj2 : j = 2 <;> simpa only [hj2, ite_true, ite_false, one_mul, zero_mul, mul_zero] using h

theorem r11b_weakAngular_sine_equation {D : ReferenceData}
    {u d : PolarPoint → ℝ} (hder : WeakAngularDerivative D u d)
    (j : ℕ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D) :
    (j : ℝ) * (∫ r in D.a..D.b, referenceMode u j r * φ r) =
      -(∫ r in D.a..D.b,
        radialAngularMean (fun θ => d (r, θ) * sineMode j θ) * φ r) := by
  have h := hder _ (r11b_radialTest_sine hφ hφc hφs j)
  have hleft (r : ℝ) :
      radialAngularMean (fun θ => u (r, θ) *
        angularPartial (fun x : PolarPoint => φ x.1 * sineMode j x.2) (r, θ)) =
        (j : ℝ) * (referenceMode u j r * φ r) := by
    simp_rw [r11b_angularPartial_sine_test hφ]
    have heq : (fun θ => u (r, θ) * ((j : ℝ) * (φ r * cosineMode j θ))) =
        (fun θ => (u (r, θ) * cosineMode j θ) * ((j : ℝ) * φ r)) := by
      funext θ
      ring
    rw [heq, r11b_radialAngularMean_mul_const]
    unfold referenceMode
    ring
  have hright (r : ℝ) :
      radialAngularMean (fun θ => d (r, θ) * (φ r * sineMode j θ)) =
        radialAngularMean (fun θ => d (r, θ) * sineMode j θ) * φ r :=
    r11b_radialAngularMean_lift_pairing (fun θ => d (r, θ)) (sineMode j) (φ r)
  change (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) *
    angularPartial (fun x : PolarPoint => φ x.1 * sineMode j x.2) (r, θ))) =
      -(∫ r in D.a..D.b, radialAngularMean (fun θ =>
        d (r, θ) * (φ r * sineMode j θ))) at h
  simp_rw [hleft, hright] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact h

end ContinuousFlexibility.Radial
