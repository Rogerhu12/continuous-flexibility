import ContinuousFlexibility.Analysis.RootFlowParameterDerivative
import ContinuousFlexibility.Analysis.ParameterizedCircleInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The root-parameter derivative of the actual inverse coordinate

The forward root flow has its genuine derivative in the independent
root parameter. The actual circle inverse is jointly smooth by the
parameterized inverse theorem. Differentiating its exact right-inverse
identity at the zero parameters determines the inverse derivative.
Composing with the prescribed angular normalization then gives the
positive root coefficient (2/3) c₀(0, θ) hL'(θ).

The inverse and coordinate derivatives are conclusions, not input
regularity assumptions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

/-- If the forward family is the identity at the zero parameters, the
actual inverse's second-parameter derivative is the negative of the
actual forward derivative. Smoothness of the inverse is derived. -/
theorem parameterizedCircleInverse_hasDerivAt_sndParameter_zero
    {F : (ℝ × ℝ) × ℝ → ℝ} {T θ k : ℝ}
    (hT : T ≠ 0) (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z : (ℝ × ℝ) × ℝ,
      0 < deriv (fun η => F (z.1, η)) z.2)
    (hperiod : ∀ p η, F (p, η + T) = F (p, η) + T)
    (hzero : ∀ η : ℝ, F ((0, 0), η) = η)
    (hroot : HasDerivAt (fun ζ : ℝ => F ((0, ζ), θ)) k 0) :
    HasDerivAt (fun ζ : ℝ => parameterizedCircleInverse F ((0, ζ), θ)) (-k) 0 := by
  let I : (ℝ × ℝ) × ℝ → ℝ := parameterizedCircleInverse F
  have hI : ContDiff ℝ ∞ I :=
    contDiff_parameterizedCircleInverse hT hF hpositive hperiod
  have hI0 : I ((0, 0), θ) = θ := by
    have hr := parameterizedCircleInverse_right_inverse hT hF hperiod ((0, 0), θ)
    exact (hzero (I ((0, 0), θ))).symm.trans hr
  let D : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ := fderiv ℝ F ((0, 0), θ)
  have hD : HasFDerivAt F D ((0, 0), θ) :=
    (hF.differentiable (by simp) _).hasFDerivAt
  have hz : D ((0, 1), 0) = k := by
    have hp : HasDerivAt (fun ζ : ℝ => (((0 : ℝ), ζ), θ))
        (((0 : ℝ), 1), 0) 0 :=
      ((hasDerivAt_const 0 (0 : ℝ)).prodMk (hasDerivAt_id 0)).prodMk
        (hasDerivAt_const 0 θ)
    have hh := hD.comp_hasDerivAt 0 hp
    have he : F ∘ (fun ζ : ℝ => (((0 : ℝ), ζ), θ)) =
        (fun ζ : ℝ => F ((0, ζ), θ)) := by
      funext ζ
      exact Function.comp_apply
    rw [he] at hh
    exact hh.unique hroot
  have hangle : HasDerivAt (fun η : ℝ => F ((0, 0), η)) 1 θ := by
    have he : (fun η : ℝ => F ((0, 0), η)) = id := by
      funext η
      exact hzero η
    rw [he]
    exact hasDerivAt_id θ
  have hθ : D ((0, 0), 1) = 1 := by
    have hp : HasDerivAt (fun η : ℝ => (((0, 0) : ℝ × ℝ), η))
        (((0, 0) : ℝ × ℝ), 1) θ :=
      (hasDerivAt_const θ ((0, 0) : ℝ × ℝ)).prodMk (hasDerivAt_id θ)
    have hh := hD.comp_hasDerivAt θ hp
    have he : F ∘ (fun η : ℝ => (((0, 0) : ℝ × ℝ), η)) =
        (fun η : ℝ => F ((0, 0), η)) := by
      funext η
      exact Function.comp_apply
    rw [he] at hh
    exact hh.unique hangle
  have hmap : ContDiff ℝ ∞ (fun ζ : ℝ => (((0 : ℝ), ζ), θ)) :=
    (contDiff_const.prodMk contDiff_id).prodMk contDiff_const
  have hcurve : ContDiff ℝ ∞ (fun ζ : ℝ => I ((0, ζ), θ)) := hI.comp hmap
  let a : ℝ := deriv (fun ζ : ℝ => I ((0, ζ), θ)) 0
  have hg : HasDerivAt (fun ζ : ℝ => I ((0, ζ), θ)) a 0 :=
    (hcurve.differentiable (by simp) 0).hasDerivAt
  have hp : HasDerivAt (fun ζ : ℝ => ((0, ζ), I ((0, ζ), θ))) ((0, 1), a) 0 :=
    ((hasDerivAt_const 0 (0 : ℝ)).prodMk (hasDerivAt_id 0)).prodMk hg
  have hcomp : HasDerivAt
      (F ∘ (fun ζ : ℝ => ((0, ζ), I ((0, ζ), θ))))
      (D ((0, 1), a)) 0 := by
    have hD' : HasFDerivAt F D ((0, 0), I ((0, 0), θ)) := by
      simpa only [hI0] using hD
    exact hD'.comp_hasDerivAt 0 hp
  have he : F ∘ (fun ζ : ℝ => ((0, ζ), I ((0, ζ), θ))) =
      (fun _ : ℝ => θ) := by
    funext ζ
    simpa only [Function.comp_apply, I] using
      parameterizedCircleInverse_right_inverse hT hF hperiod ((0, ζ), θ)
  rw [he] at hcomp
  have hv0 : D ((0, 1), a) = 0 := hcomp.unique (hasDerivAt_const 0 θ)
  have hv : (((0, 1) : ℝ × ℝ), a) =
      (((0, 1) : ℝ × ℝ), (0 : ℝ)) + a • (((0, 0) : ℝ × ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hEval : D ((0, 1), a) = k + a := by
    rw [hv, map_add, map_smul, hz, hθ, smul_eq_mul, mul_one]
  have ha : a = -k := by
    rw [hEval] at hv0
    linarith
  exact hg.congr_deriv ha

section ActualRootFlow

variable {d c₀ : ℝ × ℝ → ℝ}
  {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {T : ℝ}
  (hT : T ≠ 0) (hc₀ : ContDiff ℝ ∞ c₀)
  (hinit : ∀ p θ, Θ p 0 θ = θ)
  (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
    HasDerivWithinAt (fun r => Θ p r θ)
      (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
        2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
      (Icc (0 : ℝ) 1) t)
  (hΘ : ContinuousOn
    (fun q : ((ℝ × ℝ) × ℝ) × ℝ => Θ q.1.1 q.2 q.1.2)
    (univ ×ˢ Icc (0 : ℝ) 1))
  (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2))
  (hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ)
  (hperiod : ∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T)

include hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod

/-- The actual inverse endpoint map has the negative forcing derivative
at zero radial and root parameters. The endpoint regularity, positivity,
and periodicity are the properties produced by the smooth-flow factory. -/
theorem rootRegularizedInverse_hasDerivAt_rootParameter_zero (θ : ℝ) :
    HasDerivAt
      (fun ζ : ℝ => parameterizedCircleInverse
        (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((0, ζ), θ))
      (-(((2 : ℝ) / 3) * c₀ (0, θ))) 0 := by
  exact parameterizedCircleInverse_hasDerivAt_sndParameter_zero hT hEndpoint
    (fun z => hpositive z.1 z.2) hperiod
    (fun η => rootRegularizedFlow_zero_parameters hinit hflow η ⟨zero_le_one, le_rfl⟩)
    (rootRegularizedFlow_hasDerivAt_rootParameter_zero hc₀ hinit hflow hΘ θ)

/-- Composing the actual inverse with the fixed angular normalization
gives the claimed signed root derivative, with no coordinate smoothness
assumption. -/
theorem rootRegularizedCoordinate_hasDerivAt_rootParameter_zero
    {hL : ℝ → ℝ} (hhL : ContDiff ℝ ∞ hL) (θ : ℝ) :
    HasDerivAt
      (fun ζ : ℝ => hL (parameterizedCircleInverse
        (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((0, ζ), θ)))
      (-(((2 : ℝ) / 3) * c₀ (0, θ) * deriv hL θ)) 0 := by
  have hi := rootRegularizedInverse_hasDerivAt_rootParameter_zero
    hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod θ
  have hI0 : parameterizedCircleInverse
      (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((0, 0), θ) = θ := by
    have hr := parameterizedCircleInverse_right_inverse hT hEndpoint hperiod ((0, 0), θ)
    exact (rootRegularizedFlow_zero_parameters hinit hflow _
      (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)).symm.trans hr
  have hl : HasDerivAt hL (deriv hL θ)
      (parameterizedCircleInverse
        (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((0, 0), θ)) := by
    rw [hI0]
    exact (hhL.differentiable (by simp) θ).hasDerivAt
  have hc := hl.comp 0 hi
  have he : hL ∘ (fun ζ : ℝ => parameterizedCircleInverse
      (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((0, ζ), θ)) =
      (fun ζ : ℝ => hL (parameterizedCircleInverse
        (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((0, ζ), θ))) := by
    funext ζ
    exact Function.comp_apply
  rw [he] at hc
  exact hc.congr_deriv (by ring)

/-- The coefficient obtained by negating the actual root derivative is
exactly the positive product prescribed by the root characteristic. -/
theorem rootRegularizedCoordinate_neg_deriv_rootParameter_zero
    {hL : ℝ → ℝ} (hhL : ContDiff ℝ ∞ hL) (θ : ℝ) :
    -deriv (fun ζ : ℝ => hL (parameterizedCircleInverse
      (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((0, ζ), θ))) 0 =
        ((2 : ℝ) / 3) * c₀ (0, θ) * deriv hL θ := by
  rw [(rootRegularizedCoordinate_hasDerivAt_rootParameter_zero
    hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ).deriv, neg_neg]

/-- Positivity of the root characteristic and of the actual angular
normalization gives strict positivity of the actual root coefficient. -/
theorem rootRegularizedCoordinate_neg_deriv_rootParameter_zero_pos
    {hL : ℝ → ℝ} (hhL : ContDiff ℝ ∞ hL) (θ : ℝ)
    (hcpos : 0 < c₀ (0, θ)) (hlpos : 0 < deriv hL θ) :
    0 < -deriv (fun ζ : ℝ => hL (parameterizedCircleInverse
      (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((0, ζ), θ))) 0 := by
  rw [rootRegularizedCoordinate_neg_deriv_rootParameter_zero
    hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ]
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) hcpos) hlpos

end ActualRootFlow
end ContinuousFlexibility.Analysis
