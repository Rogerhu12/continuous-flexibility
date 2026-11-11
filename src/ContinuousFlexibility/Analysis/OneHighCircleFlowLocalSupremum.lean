import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalBounds

/-!
# Literal local-time supremum bounds

The supremum ranges over the complete original closed time interval.
The displayed circle functions are the canonical actual derivative defect
and translation displacement. The constants use only the original
locally smooth speed's integrated norms.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {G Θ : PolarPoint → ℝ} {a b ε : ℝ}
  (hε : 0 < ε)
  (hG : ContDiffOn ℝ ∞ G (Ioo (a - ε) (b + ε) ×ˢ (univ : Set ℝ)))
  (hperiod : ∀ t ∈ Ioo (a - ε) (b + ε),
    Function.Periodic (fun θ => G (t, θ)) P)
  (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
  (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
  (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
    HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)

theorem circleFlow_defect_sobolev_sup_le_local (hab : a ≤ b) (s : ℕ) :
    sSup (range (fun t : Icc a b => circleRealSobolevNorm (s : ℝ)
      (circleLiftDefectJet (fun θ => Θ (t, θ))
        (circleFlow_contDiff_angle_local hε hG hperiod hΘ hinit hflow t.property)
        (circleFlow_lift_add_local hε hG hperiod hΘ hinit hflow t.property) 0))) ≤
      circleFlowSobolevConstant P (circleFlowLocalLambda hε hG hperiod 4) s *
        circleFlowLocalLambda hε hG hperiod s := by
  apply csSup_le
  · exact ⟨_, ⟨a, ⟨le_rfl, hab⟩⟩, rfl⟩
  · rintro y ⟨t, rfl⟩
    exact circleFlow_defect_sobolev_le_local hε hG hperiod hΘ hinit hflow s t.property

theorem circleFlow_translation_sobolev_sup_le_local (hab : a ≤ b) {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) (s : ℕ) :
    sSup (range (fun t : Icc a b => circleRealSobolevNorm (s : ℝ)
      (periodicCircleJet (fun θ => Θ (t, θ) - θ - ∫ r in a..(t : ℝ), c r)
        (circleFlow_translation_periodic_local hε hG hperiod hΘ hinit hflow c t.property)
        (circleFlow_contDiff_translation_local hε hG hperiod hΘ hinit hflow c t.property) 0))) ≤
      circleFlowTranslationConstant P (circleFlowLocalLambda hε hG hperiod 4)
        (circleFlowLocalReferenceSize hε hG hperiod c 3) s *
          circleFlowLocalReferenceSize hε hG hperiod c s := by
  apply csSup_le
  · exact ⟨_, ⟨a, ⟨le_rfl, hab⟩⟩, rfl⟩
  · rintro y ⟨t, rfl⟩
    exact circleFlow_translation_sobolev_le_local hε hG hperiod hΘ hinit hflow hc s t.property

end ContinuousFlexibility.Analysis
