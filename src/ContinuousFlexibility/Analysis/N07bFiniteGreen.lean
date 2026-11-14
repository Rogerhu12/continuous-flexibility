module

public import ContinuousFlexibility.Scalar.GreenIdentity

/-!
# Finite-regularity Green identity for reference reconstruction

The actual transition charts match only finitely many jets across the
physical interfaces. A globally twice continuously differentiable height
and once continuously differentiable coefficients suffice for Green
symmetry. No infinite-order regularity is inferred from piecewise
smoothness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology

/-- One derivative of a conormal flux uses two derivatives of its height. -/
theorem n07b_c1_symmetricNormalFlux
    {A B u : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ 1 A x) (hB : ContDiffAt ℝ 1 B x)
    (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 1 (symmetricNormalFlux A B u) x :=
  (hA.mul (contDiffAt_radialPartial hu (by norm_num))).add
    (hB.mul (contDiffAt_angularPartial hu (by norm_num)))

theorem n07b_c1_symmetricAngularFlux
    {B C u : PolarPoint → ℝ} {x : PolarPoint}
    (hB : ContDiffAt ℝ 1 B x) (hC : ContDiffAt ℝ 1 C x)
    (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 1 (symmetricAngularFlux B C u) x :=
  n07b_c1_symmetricNormalFlux hB hC hu

theorem n07b_c1_symmetricGreenForm
    {A B C φ ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ 1 A x) (hB : ContDiffAt ℝ 1 B x)
    (hC : ContDiffAt ℝ 1 C x) (hφ : ContDiffAt ℝ 2 φ x)
    (hψ : ContDiffAt ℝ 2 ψ x) :
    ContDiffAt ℝ 1 (symmetricGreenForm A B C φ ψ).radial x ∧
      ContDiffAt ℝ 1 (symmetricGreenForm A B C φ ψ).angular x := by
  have hφ' : ContDiffAt ℝ 1 φ x := hφ.of_le (by norm_num)
  have hψ' : ContDiffAt ℝ 1 ψ x := hψ.of_le (by norm_num)
  exact ⟨(hψ'.mul (n07b_c1_symmetricAngularFlux hB hC hφ)).sub
      (hφ'.mul (n07b_c1_symmetricAngularFlux hB hC hψ)),
    (hφ'.mul (n07b_c1_symmetricNormalFlux hA hB hψ)).sub
      (hψ'.mul (n07b_c1_symmetricNormalFlux hA hB hφ))⟩

/-- The pointwise product rule needs precisely the displayed finite jets. -/
theorem n07b_c2_symmetric_green_identity
    {A B C φ ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ 1 A x) (hB : ContDiffAt ℝ 1 B x)
    (hC : ContDiffAt ℝ 1 C x) (hφ : ContDiffAt ℝ 2 φ x)
    (hψ : ContDiffAt ℝ 2 ψ x) :
    φ x * symmetricDivergence A B C ψ x -
        ψ x * symmetricDivergence A B C φ x =
      radialPartial (greenNormalFlux A B φ ψ) x +
        angularPartial (greenAngularFlux B C φ ψ) x := by
  have dφ := hφ.differentiableAt (by norm_num)
  have dψ := hψ.differentiableAt (by norm_num)
  have dφr := (n07b_c1_symmetricNormalFlux hA hB hφ).differentiableAt one_ne_zero
  have dψr := (n07b_c1_symmetricNormalFlux hA hB hψ).differentiableAt one_ne_zero
  have dφt := (n07b_c1_symmetricAngularFlux hB hC hφ).differentiableAt one_ne_zero
  have dψt := (n07b_c1_symmetricAngularFlux hB hC hψ).differentiableAt one_ne_zero
  unfold greenNormalFlux greenAngularFlux symmetricDivergence
  rw [radialPartial_sub
      (f := fun y => φ y * symmetricNormalFlux A B ψ y)
      (g := fun y => ψ y * symmetricNormalFlux A B φ y) (dφ.mul dψr) (dψ.mul dφr),
    angularPartial_sub
      (f := fun y => φ y * symmetricAngularFlux B C ψ y)
      (g := fun y => ψ y * symmetricAngularFlux B C φ y) (dφ.mul dψt) (dψ.mul dφt),
    radialPartial_mul dφ dψr, radialPartial_mul dψ dφr,
    angularPartial_mul dφ dψt, angularPartial_mul dψ dφt]
  simp only [symmetricNormalFlux, symmetricAngularFlux]
  ring

theorem n07b_c2_symmetric_green_identity_exterior
    {A B C φ ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ 1 A x) (hB : ContDiffAt ℝ 1 B x)
    (hC : ContDiffAt ℝ 1 C x) (hφ : ContDiffAt ℝ 2 φ x)
    (hψ : ContDiffAt ℝ 2 ψ x) :
    φ x * symmetricDivergence A B C ψ x -
        ψ x * symmetricDivergence A B C φ x =
      exteriorCoefficient (symmetricGreenForm A B C φ ψ) x := by
  have dφ := hφ.differentiableAt (by norm_num)
  have dψ := hψ.differentiableAt (by norm_num)
  have dφt := (n07b_c1_symmetricAngularFlux hB hC hφ).differentiableAt one_ne_zero
  have dψt := (n07b_c1_symmetricAngularFlux hB hC hψ).differentiableAt one_ne_zero
  rw [n07b_c2_symmetric_green_identity hA hB hC hφ hψ]
  change _ = radialPartial (greenNormalFlux A B φ ψ) x -
    angularPartial (fun y => ψ y * symmetricAngularFlux B C φ y -
      φ y * symmetricAngularFlux B C ψ y) x
  unfold greenAngularFlux
  rw [angularPartial_sub
      (f := fun y => φ y * symmetricAngularFlux B C ψ y)
      (g := fun y => ψ y * symmetricAngularFlux B C φ y) (dφ.mul dψt) (dψ.mul dφt),
    angularPartial_sub
      (f := fun y => ψ y * symmetricAngularFlux B C φ y)
      (g := fun y => φ y * symmetricAngularFlux B C ψ y) (dψ.mul dφt) (dφ.mul dψt)]
  ring

/-- Rectangle Green symmetry for C² heights and C¹ coefficients. -/
theorem n07b_c2_integral_symmetric_green_eq_zero
    {A B C φ ψ : PolarPoint → ℝ} {a b c d : ℝ}
    (hA : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ 1 A x)
    (hB : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ 1 B x)
    (hC : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ 1 C x)
    (hφ : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ 2 φ x)
    (hψ : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ 2 ψ x)
    (hseam : ∀ r ∈ uIcc a b,
      greenAngularFlux B C φ ψ (r, d) = greenAngularFlux B C φ ψ (r, c))
    (hends : ∀ θ ∈ uIcc c d,
      greenNormalFlux A B φ ψ (b, θ) = greenNormalFlux A B φ ψ (a, θ)) :
    (∫ r in a..b, ∫ θ in c..d,
      φ (r, θ) * symmetricDivergence A B C ψ (r, θ) -
        ψ (r, θ) * symmetricDivergence A B C φ (r, θ)) = 0 := by
  have hα := fun x hx => n07b_c1_symmetricGreenForm
    (hA x hx) (hB x hx) (hC x hx) (hφ x hx) (hψ x hx)
  have hp : ∀ r ∈ uIcc a b,
      (symmetricGreenForm A B C φ ψ).radial (r, d) =
        (symmetricGreenForm A B C φ ψ).radial (r, c) := by
    intro r hr
    have hs := congrArg Neg.neg (hseam r hr)
    simpa only [greenAngularFlux, symmetricGreenForm, neg_sub] using hs
  have hi := integral_exteriorCoefficient_eq_zero
    (fun x hx => (hα x hx).1) (fun x hx => (hα x hx).2) hp hends
  calc
    _ = ∫ r in a..b, ∫ θ in c..d,
        exteriorCoefficient (symmetricGreenForm A B C φ ψ) (r, θ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact n07b_c2_symmetric_green_identity_exterior
        (hA (r, θ) ⟨hr, hθ⟩) (hB (r, θ) ⟨hr, hθ⟩)
        (hC (r, θ) ⟨hr, hθ⟩) (hφ (r, θ) ⟨hr, hθ⟩) (hψ (r, θ) ⟨hr, hθ⟩)
    _ = 0 := hi

end ContinuousFlexibility.Analysis
