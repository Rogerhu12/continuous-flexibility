module

public import ContinuousFlexibility.Analysis.AdjugateAiryTransport

/-!
# Actual Airy transport for the oppositely oriented half

Reversing the canonical angular coordinate makes a negative-Jacobian
chart positive-Jacobian and leaves the Airy principal field unchanged.
The already proved transport identity therefore supplies the reversed
travel sign. All derivatives here are the actual chart derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def airyAngleReversedChart (F : PolarPoint → PolarPoint) (p : PolarPoint) : PolarPoint :=
  ((F p).1, -(F p).2)

theorem airyAngleReversedChart_fderiv_apply
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (v : PolarPoint) :
    fderiv ℝ (airyAngleReversedChart F) p v =
      ((fderiv ℝ F p v).1, -(fderiv ℝ F p v).2) := by
  have hd := hF.hasFDerivAt.fst.prodMk (hF.hasFDerivAt.snd.neg)
  change HasFDerivAt (airyAngleReversedChart F) _ p at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

theorem planeJacobian_airyAngleReversedChart
    {F : PolarPoint → PolarPoint} {p : PolarPoint} (hF : DifferentiableAt ℝ F p) :
    planeJacobian (airyAngleReversedChart F) p = -planeJacobian F p := by
  unfold planeJacobian
  rw [airyAngleReversedChart_fderiv_apply hF (1, 0),
    airyAngleReversedChart_fderiv_apply hF (0, 1)]
  ring

theorem adjugateAiry_coefficients_angleReversed
    {F : PolarPoint → PolarPoint} (h : PolarPoint → ℝ) {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) :
    (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients
        (airyAngleReversedChart F) h).a p =
      (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p ∧
    (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients
        (airyAngleReversedChart F) h).b p =
      (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).b p ∧
    (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients
        (airyAngleReversedChart F) h).c p =
      (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).c p := by
  simp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic,
    canonicalAiryPrincipalCoefficients, planeJacobian_airyAngleReversedChart hF, abs_neg,
    airyAngleReversedChart_fderiv_apply hF]
  dsimp only [airyAngleReversedChart]
  refine ⟨?_, ?_, ?_⟩ <;> ring

private theorem airyFirstIntegral_angleReversed_partials
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hξ : 0 < (F p).1) (σ : ℝ) :
    radialPartial (airyFirstIntegral (airyAngleReversedChart F) σ) p =
        -radialPartial (airyFirstIntegral F (-σ)) p ∧
      angularPartial (airyFirstIntegral (airyAngleReversedChart F) σ) p =
        -angularPartial (airyFirstIntegral F (-σ)) p := by
  have hG : DifferentiableAt ℝ (airyAngleReversedChart F) p := hF.fst.prodMk (hF.snd.neg)
  have hfirst := airyFirstIntegral_partials hG hξ σ
  have hsecond := airyFirstIntegral_partials hF hξ (-σ)
  rw [hfirst.1, hfirst.2, hsecond.1, hsecond.2,
    airyAngleReversedChart_fderiv_apply hF (1, 0),
    airyAngleReversedChart_fderiv_apply hF (0, 1)]
  dsimp only [airyAngleReversedChart]
  constructor <;> ring

/-- On a negative-Jacobian half, the minus characteristic preserves
η minus Airy travel, and the plus characteristic preserves η plus travel.
This is derived by an actual angular reversal of the chart. -/
theorem airyFirstIntegral_characteristic_transport_of_negJacobian
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hJ : planeJacobian F p < 0)
    (hh : h p ≠ 0) (hξ : 0 < (F p).1)
    (ha : (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p ≠ 0) :
    radialPartial (airyFirstIntegral F (-1)) p =
        -minusCharacteristicSpeed
          (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h) p *
          angularPartial (airyFirstIntegral F (-1)) p ∧
      radialPartial (airyFirstIntegral F 1) p =
        -plusCharacteristicSpeed
          (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h) p *
          angularPartial (airyFirstIntegral F 1) p := by
  have hG : DifferentiableAt ℝ (airyAngleReversedChart F) p := hF.fst.prodMk (hF.snd.neg)
  have hJG : 0 < planeJacobian (airyAngleReversedChart F) p := by
    rw [planeJacobian_airyAngleReversedChart hF]
    exact neg_pos.mpr hJ
  have hcoeff := adjugateAiry_coefficients_angleReversed h hF
  have haG : (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients
      (airyAngleReversedChart F) h).a p ≠ 0 := by rw [hcoeff.1]; exact ha
  have htransport := airyFirstIntegral_characteristic_transport hG hJG hh hξ haG
  have hm := airyFirstIntegral_angleReversed_partials hF hξ 1
  have hp := airyFirstIntegral_angleReversed_partials hF hξ (-1)
  simp only [neg_neg] at hp
  rw [hm.1, hm.2, hp.1, hp.2] at htransport
  simp only [minusCharacteristicSpeed, plusCharacteristicSpeed, hcoeff.1,
    hcoeff.2.1, hcoeff.2.2] at htransport ⊢
  constructor
  · linear_combination -htransport.1
  · linear_combination -htransport.2

/-- A single orientation and characteristic-sign interface covers both
halves and both true characteristic families. -/
theorem airyFirstIntegral_signed_characteristic_transport
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (side : Bool)
    (hJ : if side then planeJacobian F p < 0 else 0 < planeJacobian F p)
    (hh : h p ≠ 0) (hξ : 0 < (F p).1)
    (ha : (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p ≠ 0)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    radialPartial (airyFirstIntegral F (if side then -σ else σ)) p =
      -((adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).b p /
          (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p -
        σ * Real.sqrt
          ((adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).b p ^ 2 -
            (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p *
              (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).c p) /
          (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F h).a p) *
        angularPartial (airyFirstIntegral F (if side then -σ else σ)) p := by
  cases side with
  | false =>
      have ht := airyFirstIntegral_characteristic_transport hF hJ hh hξ ha
      rcases hσ with rfl | rfl
      · simpa only [Bool.false_eq_true, ↓reduceIte, minusCharacteristicSpeed, one_mul] using ht.1
      · simpa only [Bool.false_eq_true, ↓reduceIte, plusCharacteristicSpeed,
          neg_one_mul, neg_div, sub_neg_eq_add] using ht.2
  | true =>
      have ht := airyFirstIntegral_characteristic_transport_of_negJacobian hF hJ hh hξ ha
      rcases hσ with rfl | rfl
      · simpa only [↓reduceIte, minusCharacteristicSpeed, one_mul] using ht.1
      · simpa only [↓reduceIte, neg_neg, plusCharacteristicSpeed,
          neg_one_mul, neg_div, sub_neg_eq_add] using ht.2

end ContinuousFlexibility.Analysis
