module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowCircleFamilies
public import ContinuousFlexibility.Analysis.OneHighCircleFlowReferenceIntegrability

/-!
# Actual translation-displacement circle jets

The difference of the degree-one flow lift and the identity is
periodic. Subtracting the primitive of an angle-independent reference
speed gives precisely the displacement from the reference translation.
All circle representatives use the existing canonical periodic jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

variable {P : ℝ} [hP : Fact (0 < P)]
  {G Θ : PolarPoint → ℝ} {a b : ℝ}
  (hG : ContDiff ℝ ∞ G)
  (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
  (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
  (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
  (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
    HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)

include hG hperiod hΘ hinit hflow

theorem circleFlow_displacement_periodic {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Periodic (fun θ => Θ (t, θ) - θ) P := by
  intro θ
  dsimp only
  rw [circleFlow_lift_add hG hperiod hΘ hinit hflow ht θ]
  ring

theorem circleFlow_contDiff_displacement_angle {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (fun θ => Θ (t, θ) - θ) :=
  (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht).sub contDiff_id

def circleFlowDisplacementJet (t : ℝ) (n : ℕ) : C(AddCircle P, ℝ) :=
  if ht : t ∈ Icc a b then
    periodicCircleJet (fun θ => Θ (t, θ) - θ)
      (circleFlow_displacement_periodic hG hperiod hΘ hinit hflow ht)
      (circleFlow_contDiff_displacement_angle hG hperiod hΘ hinit hflow ht) n
  else 0

theorem circleFlowDisplacementJet_eq {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) :
    circleFlowDisplacementJet hG hperiod hΘ hinit hflow t n =
      periodicCircleJet (fun θ => Θ (t, θ) - θ)
        (circleFlow_displacement_periodic hG hperiod hΘ hinit hflow ht)
        (circleFlow_contDiff_displacement_angle hG hperiod hΘ hinit hflow ht) n := by
  simp only [circleFlowDisplacementJet, dif_pos ht]

theorem circleFlowDisplacementJet_coe_apply {t : ℝ} (ht : t ∈ Icc a b)
    (n : ℕ) (θ : ℝ) :
    circleFlowDisplacementJet hG hperiod hΘ hinit hflow t n (θ : AddCircle P) =
      iteratedDeriv n (fun η => Θ (t, η)) θ - iteratedDeriv n (id : ℝ → ℝ) θ := by
  rw [circleFlowDisplacementJet_eq hG hperiod hΘ hinit hflow ht]
  simp only [periodicCircleJet_coe_apply]
  exact iteratedDeriv_fun_sub (n := n)
    ((circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht).contDiffAt.of_le (by simp))
    contDiffAt_id

theorem circleFlowDisplacementJet_hasDerivAt {t : ℝ} (ht : t ∈ Icc a b)
    (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun η : ℝ =>
      circleFlowDisplacementJet hG hperiod hΘ hinit hflow t n (η : AddCircle P))
      (circleFlowDisplacementJet hG hperiod hΘ hinit hflow t (n + 1) (θ : AddCircle P)) θ := by
  simp only [circleFlowDisplacementJet_eq hG hperiod hΘ hinit hflow ht]
  exact periodicCircleJet_hasDerivAt _ _ _ _ _

/-- Jets of the actual flow minus the reference translation. -/
def circleFlowTranslationJet (c : ℝ → ℝ) (t : ℝ) (n : ℕ) : C(AddCircle P, ℝ) :=
  circleSubtractConstantJet (circleFlowDisplacementJet hG hperiod hΘ hinit hflow t)
    (∫ r in a..t, c r) n

theorem circleFlowTranslationJet_eq (c : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc a b) (n : ℕ) :
    circleFlowTranslationJet hG hperiod hΘ hinit hflow c t n =
      periodicCircleJet (fun θ => Θ (t, θ) - θ - ∫ r in a..t, c r)
        (circle_periodic_sub_const
          (circleFlow_displacement_periodic hG hperiod hΘ hinit hflow ht) (∫ r in a..t, c r))
        ((circleFlow_contDiff_displacement_angle hG hperiod hΘ hinit hflow ht).sub contDiff_const) n := by
  have he : circleFlowDisplacementJet hG hperiod hΘ hinit hflow t =
      periodicCircleJet (fun θ => Θ (t, θ) - θ)
        (circleFlow_displacement_periodic hG hperiod hΘ hinit hflow ht)
        (circleFlow_contDiff_displacement_angle hG hperiod hΘ hinit hflow ht) :=
    funext (circleFlowDisplacementJet_eq hG hperiod hΘ hinit hflow ht)
  rw [circleFlowTranslationJet, he]
  exact periodicCircleJet_sub_const _ _ _ _ _

theorem circleFlowTranslationJet_coe_apply (c : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc a b) (n : ℕ) (θ : ℝ) :
    circleFlowTranslationJet hG hperiod hΘ hinit hflow c t n (θ : AddCircle P) =
      iteratedDeriv n (fun η => Θ (t, η)) θ - iteratedDeriv n (id : ℝ → ℝ) θ -
        if n = 0 then ∫ r in a..t, c r else 0 := by
  simp only [circleFlowTranslationJet, circleSubtractConstantJet_apply,
    circleFlowDisplacementJet_coe_apply hG hperiod hΘ hinit hflow ht]

theorem circleFlowTranslationJet_hasDerivAt (c : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc a b) (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun η : ℝ =>
      circleFlowTranslationJet hG hperiod hΘ hinit hflow c t n (η : AddCircle P))
      (circleFlowTranslationJet hG hperiod hΘ hinit hflow c t (n + 1) (θ : AddCircle P)) θ :=
  circleSubtractConstantJet_hasDerivAt
    (circleFlowDisplacementJet hG hperiod hΘ hinit hflow t)
    (circleFlowDisplacementJet_hasDerivAt hG hperiod hΘ hinit hflow ht) _ _ _

end ContinuousFlexibility.Analysis
