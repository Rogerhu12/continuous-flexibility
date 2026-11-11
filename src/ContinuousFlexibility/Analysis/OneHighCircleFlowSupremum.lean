import ContinuousFlexibility.Analysis.OneHighCircleFlowTranslationBounds

/-!
# Literal time-supremum forms of the circle-flow estimates

The proved uniform bounds include both physical time endpoints. Taking the
supremum over the closed time interval preserves the same constants, without
adding a norm or differentiability assumption on the flow.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {G Θ : PolarPoint → ℝ} {a b : ℝ}
  (hG : ContDiff ℝ ∞ G)
  (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
  (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
  (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
  (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
    HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)

/-- The second displayed assertion of the circle-flow lemma, with the
supremum taken over the complete closed time interval. -/
theorem circleFlow_defect_sobolev_sup_le (hab : a ≤ b) (s : ℕ) :
    sSup ((fun t => circleRealSobolevNorm (s : ℝ)
      (circleFlowDefectJet hG hperiod hΘ hinit hflow t 0)) '' Icc a b) ≤
      circleFlowSobolevConstant P (circleFlowLambda G hG hperiod 4 a b) s *
        circleFlowLambda G hG hperiod s a b := by
  apply csSup_le
  · exact ⟨_, a, ⟨le_rfl, hab⟩, rfl⟩
  · rintro y ⟨t, ht, rfl⟩
    exact circleFlow_defect_sobolev_le hG hperiod hΘ hinit hflow s ht

/-- The comparison with an angularly constant speed, in the manuscript's
literal supremum form. The reference speed needs only time integrability. -/
theorem circleFlow_translation_sobolev_sup_le (hab : a ≤ b) {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) (s : ℕ) :
    sSup ((fun t => circleRealSobolevNorm (s : ℝ)
      (circleFlowTranslationJet hG hperiod hΘ hinit hflow c t 0)) '' Icc a b) ≤
      circleFlowTranslationConstant P (circleFlowLambda G hG hperiod 4 a b)
        (circleFlowReferenceSize G hG hperiod c 3 a b) s *
          circleFlowReferenceSize G hG hperiod c s a b := by
  apply csSup_le
  · exact ⟨_, a, ⟨le_rfl, hab⟩, rfl⟩
  · rintro y ⟨t, ht, rfl⟩
    exact circleFlow_translation_sobolev_le hG hperiod hΘ hinit hflow hc s ht

end ContinuousFlexibility.Analysis
