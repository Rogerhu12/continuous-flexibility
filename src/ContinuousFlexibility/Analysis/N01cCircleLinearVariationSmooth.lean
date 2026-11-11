import ContinuousFlexibility.Analysis.N01cCircleLinearVariationBounds
import ContinuousFlexibility.Analysis.OneHighCircleFlowSpeedNorms

/-!
# The Sobolev bound from a genuine smooth linear variational equation

Joint smoothness commutes time and angular derivatives, so the ordinary
scalar equation alone supplies every time equation required by the
Sobolev estimate.  All circle functions are the existing canonical
descents of the actual angular derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

/-- Commutation of the actual angular jets with the given time equation.
Only the order-zero time equation is a hypothesis. -/
theorem smoothLinearVariation_hasDerivAt_angularJet_time
    {Y A F : PolarPoint → ℝ} {a b : ℝ}
    (hY : ContDiff ℝ ∞ Y)
    (hode : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Y (r, θ)) (A (t, θ) * Y (t, θ) + F (t, θ)) t)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) (θ : ℝ) :
    HasDerivAt (fun r => iteratedDeriv n (fun η => Y (r, η)) θ)
      (iteratedDeriv n (fun η => A (t, η) * Y (t, η) + F (t, η)) θ) t := by
  have hjet : ContDiff ℝ ∞ (Statements.mixedDerivative 0 n Y) :=
    contDiffOn_univ.mp
      (Statements.contDiffOn_mixedDerivative isOpen_univ hY.contDiffOn 0 n)
  have hd0 := (hjet.differentiable (by simp) (t, θ)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t θ))
  have heval : (Statements.mixedDerivative 0 n Y ∘ (fun r : ℝ => (id r, θ))) =
      fun r => iteratedDeriv n (fun η => Y (r, η)) θ := by
    funext r
    simp only [Function.comp_apply, id_eq, Statements.mixedDerivative, iteratedDeriv_zero]
  rw [heval] at hd0
  have hd : HasDerivAt (fun r => iteratedDeriv n (fun η => Y (r, η)) θ)
      (deriv (fun r => iteratedDeriv n (fun η => Y (r, η)) θ) t) t :=
    hd0.differentiableAt.hasDerivAt
  have heq : (fun η => radialPartial Y (t, η)) =
      fun η => A (t, η) * Y (t, η) + F (t, η) := by
    funext η
    have hpartial : HasDerivAt (fun r => Y (r, η)) (radialPartial Y (t, η)) t :=
      (hY.differentiable (by simp) (t, η)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t η))
    exact hpartial.unique (hode t ht η)
  have hcomm := Statements.mixedDerivative_radialPartial
    isOpen_univ hY.contDiffOn 0 n (p := (t, θ)) (mem_univ _)
  apply hd.congr_deriv
  simpa only [Statements.mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one,
    Nat.zero_add, heq] using hcomm.symm

/-- Canonical circle data built from the actual smooth functions and
their ordinary linear time equation. No differentiated equation or
Sobolev bound is assumed. -/
def circleLinearVariationOfSmooth
    {Y A F : PolarPoint → ℝ} {a b : ℝ}
    (hY : ContDiff ℝ ∞ Y) (hA : ContDiff ℝ ∞ A) (hF : ContDiff ℝ ∞ F)
    (hYperiod : ∀ t : ℝ, Function.Periodic (fun θ => Y (t, θ)) P)
    (hAperiod : ∀ t : ℝ, Function.Periodic (fun θ => A (t, θ)) P)
    (hFperiod : ∀ t : ℝ, Function.Periodic (fun θ => F (t, θ)) P)
    (hinit : ∀ θ : ℝ, Y (a, θ) = 0)
    (hode : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Y (r, θ)) (A (t, θ) * Y (t, θ) + F (t, θ)) t) :
    CircleLinearVariationData P a b := by
  let R : PolarPoint → ℝ := fun p => A p * Y p + F p
  have hR : ContDiff ℝ ∞ R := (hA.mul hY).add hF
  have hRperiod : ∀ t : ℝ, Function.Periodic (fun θ => R (t, θ)) P :=
    fun t => ((hAperiod t).mul (hYperiod t)).add (hFperiod t)
  refine
    { value := circleFlowSpeedJet Y hY hYperiod
      coefficient := circleFlowSpeedJet A hA hAperiod
      forcing := circleFlowSpeedJet F hF hFperiod
      source := circleFlowSpeedJet R hR hRperiod
      value_derivative := fun t _ => circleFlowSpeedJet_hasDerivAt Y hY hYperiod t
      coefficient_derivative := fun t _ => circleFlowSpeedJet_hasDerivAt A hA hAperiod t
      forcing_derivative := fun t _ => circleFlowSpeedJet_hasDerivAt F hF hFperiod t
      source_derivative := fun t _ => circleFlowSpeedJet_hasDerivAt R hR hRperiod t
      value_continuous := fun n => (continuous_circleFlowSpeedJet Y hY hYperiod n).continuousOn
      coefficient_continuous := fun n =>
        (continuous_circleFlowSpeedJet A hA hAperiod n).continuousOn
      forcing_continuous := fun n => (continuous_circleFlowSpeedJet F hF hFperiod n).continuousOn
      source_continuous := fun n => (continuous_circleFlowSpeedJet R hR hRperiod n).continuousOn
      initial := ?_
      equation := ?_
      source_eq := ?_ }
  · intro n
    ext θ
    induction θ using QuotientAddGroup.induction_on
    rename_i η
    have he : (fun θ => Y (a, θ)) = fun _ => (0 : ℝ) := funext hinit
    simp only [circleFlowSpeedJet_coe_apply, ContinuousMap.zero_apply, he,
      iteratedDeriv_const, ite_self]
  · intro t ht n θ
    induction θ using QuotientAddGroup.induction_on
    rename_i η
    simpa only [circleFlowSpeedJet_coe_apply, R] using
      smoothLinearVariation_hasDerivAt_angularJet_time hY hode n ht η
  · intro t _
    ext θ
    induction θ using QuotientAddGroup.induction_on
    rename_i η
    simp only [circleFlowSpeedJet_coe_apply, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, iteratedDeriv_zero, R]

/-- The high Sobolev bound for the genuine solution of a smooth,
periodic, scalar linear variational equation.  The coefficient and
forcing integrals on the right are their actual physical circle norms. -/
theorem circleLinearVariationOfSmooth_sobolev_le
    {Y A F : PolarPoint → ℝ} {a b : ℝ}
    (hY : ContDiff ℝ ∞ Y) (hA : ContDiff ℝ ∞ A) (hF : ContDiff ℝ ∞ F)
    (hYperiod : ∀ t : ℝ, Function.Periodic (fun θ => Y (t, θ)) P)
    (hAperiod : ∀ t : ℝ, Function.Periodic (fun θ => A (t, θ)) P)
    (hFperiod : ∀ t : ℝ, Function.Periodic (fun θ => F (t, θ)) P)
    (hinit : ∀ θ : ℝ, Y (a, θ) = 0)
    (hode : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Y (r, θ)) (A (t, θ) * Y (t, θ) + F (t, θ)) t)
    (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ) (circleFlowSpeedJet Y hY hYperiod t 0) ≤
      circleLinearVariationSobolevConstant P
        (∫ r in a..b, circleRealSobolevNorm 1 (circleFlowSpeedJet A hA hAperiod r 0)) s *
        ((∫ r in a..b, circleRealSobolevNorm (s : ℝ)
          (circleFlowSpeedJet F hF hFperiod r 0)) +
          (∫ r in a..b, circleRealSobolevNorm (s : ℝ)
            (circleFlowSpeedJet A hA hAperiod r 0)) *
          ∫ r in a..b, circleRealSobolevNorm 1 (circleFlowSpeedJet F hF hFperiod r 0)) := by
  exact (circleLinearVariationOfSmooth hY hA hF hYperiod hAperiod hFperiod hinit hode).sobolev_le s ht

/-- The actual angular derivatives satisfy the same one-high estimate,
with a single additional Sobolev order. -/
theorem circleLinearVariationOfSmooth_angular_le
    {Y A F : PolarPoint → ℝ} {a b : ℝ}
    (hY : ContDiff ℝ ∞ Y) (hA : ContDiff ℝ ∞ A) (hF : ContDiff ℝ ∞ F)
    (hYperiod : ∀ t : ℝ, Function.Periodic (fun θ => Y (t, θ)) P)
    (hAperiod : ∀ t : ℝ, Function.Periodic (fun θ => A (t, θ)) P)
    (hFperiod : ∀ t : ℝ, Function.Periodic (fun θ => F (t, θ)) P)
    (hinit : ∀ θ : ℝ, Y (a, θ) = 0)
    (hode : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Y (r, θ)) (A (t, θ) * Y (t, θ) + F (t, θ)) t)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    |iteratedDeriv n (fun η => Y (t, η)) θ| ≤ circleSobolevEmbeddingConstant P *
      circleLinearVariationSobolevConstant P
        (∫ r in a..b, circleRealSobolevNorm 1 (circleFlowSpeedJet A hA hAperiod r 0)) (n + 1) *
        ((∫ r in a..b, circleRealSobolevNorm ((n + 1 : ℕ) : ℝ)
          (circleFlowSpeedJet F hF hFperiod r 0)) +
          (∫ r in a..b, circleRealSobolevNorm ((n + 1 : ℕ) : ℝ)
            (circleFlowSpeedJet A hA hAperiod r 0)) *
          ∫ r in a..b, circleRealSobolevNorm 1 (circleFlowSpeedJet F hF hFperiod r 0)) := by
  have h := (circleLinearVariationOfSmooth hY hA hF hYperiod hAperiod hFperiod hinit hode).angular_value_le n ht (θ : AddCircle P)
  change |circleFlowSpeedJet Y hY hYperiod t n (θ : AddCircle P)| ≤ _ at h
  simpa only [circleFlowSpeedJet_coe_apply] using h

end ContinuousFlexibility.Analysis

