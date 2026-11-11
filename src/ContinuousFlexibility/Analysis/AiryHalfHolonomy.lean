import ContinuousFlexibility.Analysis.AdjugateAiryTransport
import ContinuousFlexibility.Geometry.Primitive
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Half-strip holonomy from an actual Airy chart and actual trajectories

The endpoint transport identity is a consequence of the chain rule and
the mean value theorem. The two characteristic families then give a
roundtrip conjugate to translation by minus twice the Airy travel width.
The root angular normalization cancels; no equality with another half's
boundary normalization and no prescribed boundary inverse are used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Interior transport plus genuine endpoint continuity gives equality
of the values at the endpoints of an actual characteristic. -/
theorem endpoint_eq_of_characteristic_transport
    {U : PolarPoint → ℝ} {u v : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hcont : ContinuousOn (fun r => U (r, u r)) (Icc a b))
    (hU : ∀ r ∈ Ioo a b, DifferentiableAt ℝ U (r, u r))
    (hflow : ∀ r ∈ Ioo a b, HasDerivAt u (v r) r)
    (htransport : ∀ r ∈ Ioo a b,
      radialPartial U (r, u r) = -v r * angularPartial U (r, u r)) :
    U (b, u b) = U (a, u a) := by
  have hd (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt (fun t => U (t, u t)) 0 r := by
    have hpath : HasDerivAt (fun t : ℝ => (t, u t)) (1, v r) r :=
      (hasDerivAt_id r).prodMk (hflow r hr)
    have hh := (hU r hr).hasFDerivAt.comp_hasDerivAt r hpath
    have he : U ∘ (fun t : ℝ => (t, u t)) = (fun t : ℝ => U (t, u t)) := by
      funext t
      exact Function.comp_apply
    rw [he] at hh
    apply hh.congr_deriv
    rw [polarCLM_apply_decompose]
    change 1 * radialPartial U (r, u r) + v r * angularPartial U (r, u r) = 0
    rw [htransport r hr]
    ring
  obtain ⟨r, _, hr⟩ := exists_hasDerivAt_eq_slope
    (fun t => U (t, u t)) (fun _ => 0) hab hcont hd
  have hz : 0 * (b - a) = U (b, u b) - U (a, u a) :=
    (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp hr
  linarith only [hz]

theorem continuous_airyTravelPrimitive : Continuous airyTravelPrimitive :=
  continuous_const.mul (Real.continuous_rpow_const (by norm_num : 0 ≤ (3 / 2 : ℝ)))

theorem airyTravelPrimitive_zero : airyTravelPrimitive 0 = 0 := by
  simp only [airyTravelPrimitive, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), mul_zero]

/-- One actual signed trajectory has the endpoint transport law forced
by the Airy chart. Here sign 1 denotes the minus characteristic. -/
theorem airyFirstIntegral_endpoint_of_actual_ode
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {u : ℝ → ℝ} {a b σ : ℝ}
    (hab : a < b) (hσ : σ = 1 ∨ σ = -1)
    (hcont : ContinuousOn (fun r => F (r, u r)) (Icc a b))
    (hregular : ∀ r ∈ Ioo a b,
      DifferentiableAt ℝ F (r, u r) ∧ 0 < planeJacobian F (r, u r) ∧
      h (r, u r) ≠ 0 ∧ 0 < (F (r, u r)).1 ∧
      (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a
        (r, u r) ≠ 0)
    (hflow : ∀ r ∈ Ioo a b, HasDerivAt u
      ((adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).b
          (r, u r) /
        (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a
          (r, u r) -
        σ * Real.sqrt
          ((adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).b
              (r, u r) ^ 2 -
            (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a
              (r, u r) *
            (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).c
              (r, u r)) /
          (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a
            (r, u r)) r) :
    airyFirstIntegral F σ (b, u b) = airyFirstIntegral F σ (a, u a) := by
  let B := adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h
  let v : ℝ → ℝ := fun r => B.b (r, u r) / B.a (r, u r) -
    σ * Real.sqrt (B.b (r, u r) ^ 2 - B.a (r, u r) * B.c (r, u r)) / B.a (r, u r)
  have hc : ContinuousOn (fun r => airyFirstIntegral F σ (r, u r)) (Icc a b) :=
    hcont.snd.add (continuousOn_const.mul
      (continuous_airyTravelPrimitive.comp_continuousOn hcont.fst))
  have hu (r : ℝ) (hr : r ∈ Ioo a b) :
      DifferentiableAt ℝ (airyFirstIntegral F σ) (r, u r) := by
    obtain ⟨hF, _, _, hξ, _⟩ := hregular r hr
    exact hF.snd.add (differentiableAt_const.mul
      ((hasDerivAt_airyTravelPrimitive hξ).differentiableAt.comp (r, u r) hF.fst))
  have hpde (r : ℝ) (hr : r ∈ Ioo a b) :
      radialPartial (airyFirstIntegral F σ) (r, u r) =
        -v r * angularPartial (airyFirstIntegral F σ) (r, u r) := by
    obtain ⟨hF, hJ, hh, hξ, ha⟩ := hregular r hr
    have hh := airyFirstIntegral_characteristic_transport hF hJ hh hξ ha
    rcases hσ with rfl | rfl
    · simpa only [v, B, minusCharacteristicSpeed, one_mul] using hh.1
    · simpa only [v, B, plusCharacteristicSpeed, neg_one_mul, neg_div, sub_neg_eq_add]
        using hh.2
  exact endpoint_eq_of_characteristic_transport hab hc hu hflow hpde

/-- A complete pair of true characteristics in a half strip has fixed
roundtrip translation in the cut's own angular coordinate. The root
and cut angular maps need only the actual surjectivity/injectivity
already forced by the closed chart boundary lift. -/
theorem airy_half_roundtrip_conjugacy_of_actual_flow
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {Φ : ℝ → ℝ → ℝ → ℝ} {a b ρ : ℝ}
    (hab : a < b)
    (hFcont : ContinuousOn F (Icc a b ×ˢ (univ : Set ℝ)))
    (hregular : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      DifferentiableAt ℝ F p ∧ 0 < planeJacobian F p ∧
      h p ≠ 0 ∧ 0 < (F p).1 ∧
      (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p ≠ 0)
    (hroot : ∀ θ, (F (a, θ)).1 = 0)
    (hcut : ∀ θ, (F (b, θ)).1 = ρ)
    (hrootSurj : Function.Surjective (fun θ => (F (a, θ)).2))
    (hcutInj : Function.Injective (fun θ => (F (b, θ)).2))
    (hcont : ∀ σ, σ = 1 ∨ σ = -1 → ∀ θ, ContinuousOn (Φ σ θ) (Icc a b))
    (hinit : ∀ σ, σ = 1 ∨ σ = -1 → ∀ θ, Φ σ θ a = θ)
    (hflow : ∀ σ, σ = 1 ∨ σ = -1 → ∀ θ r, r ∈ Ioo a b →
      HasDerivAt (Φ σ θ)
        ((adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).b
            (r, Φ σ θ r) /
          (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a
            (r, Φ σ θ r) -
          σ * Real.sqrt
            ((adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).b
                (r, Φ σ θ r) ^ 2 -
              (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a
                (r, Φ σ θ r) *
              (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).c
                (r, Φ σ θ r)) /
            (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a
              (r, Φ σ θ r)) r) :
    ∀ θ : ℝ,
      (F (b, Φ 1 (Function.invFun (fun η => Φ (-1) η b) θ) b)).2 =
        (F (b, θ)).2 - 2 * airyTravelPrimitive ρ := by
  have hend (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (θ : ℝ) :
      (F (b, Φ σ θ b)).2 + σ * airyTravelPrimitive ρ = (F (a, θ)).2 := by
    have hpath : ContinuousOn (fun r : ℝ => (r, Φ σ θ r)) (Icc a b) :=
      continuousOn_id.prodMk (hcont σ hσ θ)
    have hc : ContinuousOn (fun r => F (r, Φ σ θ r)) (Icc a b) :=
      hFcont.comp hpath (fun r hr => ⟨hr, mem_univ _⟩)
    have he := airyFirstIntegral_endpoint_of_actual_ode hab hσ hc
      (fun r hr => hregular (r, Φ σ θ r) ⟨hr, mem_univ _⟩) (hflow σ hσ θ)
    simpa only [airyFirstIntegral, hinit σ hσ θ, hroot, hcut,
      airyTravelPrimitive_zero, mul_zero, add_zero] using he
  have hsurj : Function.Surjective (fun η => Φ (-1) η b) := by
    intro θ
    obtain ⟨η, hη⟩ := hrootSurj ((F (b, θ)).2 - airyTravelPrimitive ρ)
    refine ⟨η, hcutInj ?_⟩
    have he := hend (-1) (Or.inr rfl) η
    change (F (b, Φ (-1) η b)).2 = (F (b, θ)).2
    linarith only [he, hη]
  intro θ
  let η : ℝ := Function.invFun (fun φ => Φ (-1) φ b) θ
  have hi : Φ (-1) η b = θ := Function.rightInverse_invFun hsurj θ
  have hm := hend 1 (Or.inl rfl) η
  have hp := hend (-1) (Or.inr rfl) η
  rw [hi] at hp
  change (F (b, Φ 1 η b)).2 = (F (b, θ)).2 - 2 * airyTravelPrimitive ρ
  linarith only [hm, hp]

end ContinuousFlexibility.Analysis

