import ContinuousFlexibility.Analysis.InteriorTravelMonotonicity

/-!
# Propagating the two true section bounds into the radial interior

The left bound uses the already constructed actual inverse endpoint map.
For the right bound a plus trajectory starts at the point being tested
and ends on the fixed right section. Ordinary periodic-flow existence
supplies that trajectory; no inverse regularity is postulated.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

section Strip

variable {a b : ℝ} {fminus fplus U V : PolarPoint → ℝ}
  (hU : ContinuousOn U (Icc a b ×ˢ (univ : Set ℝ)))
  (hV : ContinuousOn V (Icc a b ×ˢ (univ : Set ℝ)))
  (hUd : ∀ r ∈ Icc a b, ∀ θ : ℝ, DifferentiableAt ℝ U (r, θ))
  (hVd : ∀ r ∈ Icc a b, ∀ θ : ℝ, DifferentiableAt ℝ V (r, θ))
  (hminus : ∀ r ∈ Icc a b, ∀ θ : ℝ,
    radialPartial U (r, θ) = -fminus (r, θ) * angularPartial U (r, θ))
  (hplus : ∀ r ∈ Icc a b, ∀ θ : ℝ,
    radialPartial V (r, θ) = -fplus (r, θ) * angularPartial V (r, θ))
  (hspeeds : ∀ r ∈ Icc a b, ∀ θ : ℝ, fminus (r, θ) ≤ fplus (r, θ))
  (hangular : ∀ r ∈ Icc a b, ∀ θ : ℝ, 0 ≤ angularPartial U (r, θ))

include hU hV hUd hVd hminus hplus hspeeds hangular

theorem interiorTravel_lowerBound_of_leftSection
    (hab : a < b) {Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations (interiorScalarFlowField fplus a b) Θ)
    (hinverse : ∀ v θ, Θ v 1 (Ψ v 1 θ) = θ)
    {ℓ : ℝ} (hleft : ∀ θ : ℝ, ℓ ≤ (U (a, θ) - V (a, θ)) / 2)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    ℓ ≤ (U (r, θ) - V (r, θ)) / 2 := by
  let v := interiorEndpointParameter a b r
  let φ := Ψ v 1 θ
  have hmono := interiorFlow_travelDifference_monotone hab.le hΘ
    hU hV hUd hVd hminus hplus hspeeds hangular
    (interiorEndpointParameter_mem hab hr) φ
  have he := hmono (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) zero_le_one
  have hzero : interiorFlowRadius a b 0 v = a := by
    simp only [interiorFlowRadius, zero_mul, add_zero]
  have hone : interiorFlowRadius a b 1 v = r :=
    interiorFlowRadius_endpointParameter hab r
  have hstart : Θ v 0 φ = φ := hΘ.1 v φ
  have hend : Θ v 1 φ = θ := hinverse v θ
  change (U (interiorFlowRadius a b 0 v, Θ v 0 φ) -
    V (interiorFlowRadius a b 0 v, Θ v 0 φ)) / 2 ≤
    (U (interiorFlowRadius a b 1 v, Θ v 1 φ) -
      V (interiorFlowRadius a b 1 v, Θ v 1 φ)) / 2 at he
  rw [hzero, hone, hstart, hend] at he
  exact (hleft φ).trans he

theorem interiorTravel_upperBound_of_rightSection
    (hfplus : ContDiff ℝ ∞ fplus)
    (hperiod : ∀ r, Function.Periodic (fun θ => fplus (r, θ)) Real.pi)
    {u : ℝ} (hright : ∀ θ : ℝ, (U (b, θ) - V (b, θ)) / 2 ≤ u)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    (U (r, θ) - V (r, θ)) / 2 ≤ u := by
  have hsub : Icc r b ⊆ Icc a b := Icc_subset_Icc hr.1 le_rfl
  obtain ⟨Θ, hi, hd, _, _⟩ := exists_continuous_periodicScalarFlowFamily
    (F := interiorScalarFlowField fplus r b) zero_le_one Real.pi_ne_zero
    (contDiff_interiorScalarFlowField hfplus r b)
    (fun t _ => interiorScalarFlowField_periodic hperiod r b t)
  have hΘ : N04FlowEquations (interiorScalarFlowField fplus r b) Θ := ⟨hi, hd⟩
  have hv : (1, (0 : ℝ)) ∈ n04FlowParameterBox := by
    change (1 : ℝ) ∈ Icc (-1) 1 ∧ (0 : ℝ) ∈ Icc (-1) 1
    norm_num
  have hmono := interiorFlow_travelDifference_monotone hr.2 hΘ
    (hU.mono (Set.prod_mono hsub (subset_refl _)))
    (hV.mono (Set.prod_mono hsub (subset_refl _)))
    (fun s hs => hUd s (hsub hs)) (fun s hs => hVd s (hsub hs))
    (fun s hs => hminus s (hsub hs)) (fun s hs => hplus s (hsub hs))
    (fun s hs => hspeeds s (hsub hs)) (fun s hs => hangular s (hsub hs)) hv θ
  have he := hmono (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) zero_le_one
  have hzero : interiorFlowRadius r b 0 (1, 0) = r := by
    simp only [interiorFlowRadius, zero_mul, add_zero]
  have hone : interiorFlowRadius r b 1 (1, 0) = b := by
    dsimp only [interiorFlowRadius]
    ring
  have hstart : Θ (1, 0) 0 θ = θ := hΘ.1 (1, 0) θ
  change (U (interiorFlowRadius r b 0 (1, 0), Θ (1, 0) 0 θ) -
    V (interiorFlowRadius r b 0 (1, 0), Θ (1, 0) 0 θ)) / 2 ≤
    (U (interiorFlowRadius r b 1 (1, 0), Θ (1, 0) 1 θ) -
      V (interiorFlowRadius r b 1 (1, 0), Θ (1, 0) 1 θ)) / 2 at he
  rw [hzero, hone, hstart] at he
  exact he.trans (hright (Θ (1, 0) 1 θ))

end Strip

end ContinuousFlexibility.Analysis
