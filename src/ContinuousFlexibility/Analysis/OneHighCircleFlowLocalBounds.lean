import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalNorms
import ContinuousFlexibility.Analysis.OneHighCircleFlowTranslationBounds

/-!
# Circle-flow bounds from smoothness on a time neighborhood

The original speed is assumed smooth and periodic only near the given
closed time interval. A constructed localization transfers the existing
flow proofs without changing any trajectory, angular derivative, or speed
norm used in the result. The constants contain no localization margin.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable {G Θ : PolarPoint → ℝ} {a b ε : ℝ}

/-- The supplied trajectories solve the localized equation on the same
original interval; no new flow is chosen. -/
theorem circleFlow_localized_ode (hab : a ≤ b) (hε : 0 < ε)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) :
    ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ))
        (circleFlowLocalizedSpeed G hab hε (t, Θ (t, θ))) t := by
  intro t ht θ
  rw [circleFlowLocalizedSpeed_eq hab hε ⟨ht.1.le, ht.2.le⟩]
  exact hflow t ht θ

variable {P : ℝ} [hP : Fact (0 < P)]
  (hε : 0 < ε)
  (hG : ContDiffOn ℝ ∞ G (Ioo (a - ε) (b + ε) ×ˢ (univ : Set ℝ)))
  (hperiod : ∀ t ∈ Ioo (a - ε) (b + ε),
    Function.Periodic (fun θ => G (t, θ)) P)
  (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
  (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
  (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
    HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)

include hε hG hperiod hΘ hinit hflow

/-- Angular smoothness at every closed-time endpoint is derived from the
local speed and the original classical trajectory equation. -/
theorem circleFlow_contDiff_angle_local {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (fun θ => Θ (t, θ)) :=
  circleFlow_contDiff_angle
    (contDiff_circleFlowLocalizedSpeed (ht.1.trans ht.2) hε hG) hP.out
    (circleFlowLocalizedSpeed_periodic (ht.1.trans ht.2) hε hperiod)
    hΘ hinit (circleFlow_localized_ode (ht.1.trans ht.2) hε hflow) ht

theorem circleFlow_lift_add_local {t : ℝ} (ht : t ∈ Icc a b) :
    ∀ θ : ℝ, Θ (t, θ + P) = Θ (t, θ) + P :=
  circleFlow_lift_add
    (contDiff_circleFlowLocalizedSpeed (ht.1.trans ht.2) hε hG)
    (circleFlowLocalizedSpeed_periodic (ht.1.trans ht.2) hε hperiod)
    hΘ hinit (circleFlow_localized_ode (ht.1.trans ht.2) hε hflow) ht

/-- The exact variational formula uses the original speed's ordinary
angular derivative, under only local time smoothness. -/
theorem circleFlow_hasDerivAt_angle_local {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    HasDerivAt (fun η => Θ (t, η))
      (Real.exp (∫ r in a..t, deriv (fun η => G (r, η)) (Θ (r, θ)))) θ := by
  have hab : a ≤ b := ht.1.trans ht.2
  let hg := contDiff_circleFlowLocalizedSpeed hab hε hG
  let hp := circleFlowLocalizedSpeed_periodic hab hε hperiod
  let hf := circleFlow_localized_ode hab hε hflow
  have he : (∫ r in a..t,
      angularPartial (circleFlowLocalizedSpeed G hab hε) (r, Θ (r, θ))) =
      ∫ r in a..t, deriv (fun η => G (r, η)) (Θ (r, θ)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a t := by simpa only [uIcc_of_le ht.1] using hr
    have hrab : r ∈ Icc a b := ⟨hr'.1, hr'.2.trans ht.2⟩
    rw [← deriv_cylinder_angular_slice (hg.differentiable (by simp)) r (Θ (r, θ)),
      circleFlowLocalizedSpeed_slice_eq hab hε hrab]
  have h := circleFlow_hasDerivAt_angle hg hP.out hp hΘ hinit hf ht θ
  rwa [he] at h

theorem circleFlow_deriv_eq_exp_local {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    deriv (fun η => Θ (t, η)) θ =
      Real.exp (∫ r in a..t, deriv (fun η => G (r, η)) (Θ (r, θ))) :=
  (circleFlow_hasDerivAt_angle_local hε hG hperiod hΘ hinit hflow ht θ).deriv

/-- The genuine Jacobian is controlled by the original local speed's Λ₁. -/
theorem circleFlow_deriv_bounds_sobolev_local {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    Real.exp (-(circleFlowEmbeddingConstant P * circleFlowLocalLambda hε hG hperiod 1)) ≤
        deriv (fun η => Θ (t, η)) θ ∧
      deriv (fun η => Θ (t, η)) θ ≤
        Real.exp (circleFlowEmbeddingConstant P * circleFlowLocalLambda hε hG hperiod 1) := by
  have hab : a ≤ b := ht.1.trans ht.2
  have h := circleFlow_deriv_bounds_sobolev
    (contDiff_circleFlowLocalizedSpeed hab hε hG)
    (circleFlowLocalizedSpeed_periodic hab hε hperiod)
    hΘ hinit (circleFlow_localized_ode hab hε hflow) ht θ
  simpa only [circleFlowLambda_localized_eq hε hG hperiod hab] using h

/-- The actual canonical derivative defect has the same uniform high-order
bound, with no global smoothness premise on the original speed. -/
theorem circleFlow_defect_sobolev_le_local (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ)
      (circleLiftDefectJet (fun θ => Θ (t, θ))
        (circleFlow_contDiff_angle_local hε hG hperiod hΘ hinit hflow ht)
        (circleFlow_lift_add_local hε hG hperiod hΘ hinit hflow ht) 0) ≤
      circleFlowSobolevConstant P (circleFlowLocalLambda hε hG hperiod 4) s *
        circleFlowLocalLambda hε hG hperiod s := by
  have hab : a ≤ b := ht.1.trans ht.2
  let hg := contDiff_circleFlowLocalizedSpeed hab hε hG
  let hp := circleFlowLocalizedSpeed_periodic hab hε hperiod
  let hf := circleFlow_localized_ode hab hε hflow
  have h := circleFlow_defect_sobolev_le hg hp hΘ hinit hf s ht
  rw [circleFlowDefectJet_eq hg hp hΘ hinit hf ht 0] at h
  simpa only [circleFlowLambda_localized_eq hε hG hperiod hab] using h

theorem circleFlow_translation_periodic_local (c : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Periodic (fun θ => Θ (t, θ) - θ - ∫ r in a..t, c r) P := by
  intro θ
  dsimp only
  rw [circleFlow_lift_add_local hε hG hperiod hΘ hinit hflow ht θ]
  ring

theorem circleFlow_contDiff_translation_local (c : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (fun θ => Θ (t, θ) - θ - ∫ r in a..t, c r) :=
  ((circleFlow_contDiff_angle_local hε hG hperiod hΘ hinit hflow ht).sub contDiff_id).sub
    contDiff_const

/-- The exact displacement from an integrable reference translation obeys
the same estimate at every natural Sobolev order and both time endpoints.
All norms and integrated sizes refer to the original speed. -/
theorem circleFlow_translation_sobolev_le_local {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ)
      (periodicCircleJet (fun θ => Θ (t, θ) - θ - ∫ r in a..t, c r)
        (circleFlow_translation_periodic_local hε hG hperiod hΘ hinit hflow c ht)
        (circleFlow_contDiff_translation_local hε hG hperiod hΘ hinit hflow c ht) 0) ≤
      circleFlowTranslationConstant P (circleFlowLocalLambda hε hG hperiod 4)
        (circleFlowLocalReferenceSize hε hG hperiod c 3) s *
          circleFlowLocalReferenceSize hε hG hperiod c s := by
  have hab : a ≤ b := ht.1.trans ht.2
  let hg := contDiff_circleFlowLocalizedSpeed hab hε hG
  let hp := circleFlowLocalizedSpeed_periodic hab hε hperiod
  let hf := circleFlow_localized_ode hab hε hflow
  have h := circleFlow_translation_sobolev_le hg hp hΘ hinit hf hc s ht
  rw [circleFlowTranslationJet_eq hg hp hΘ hinit hf c ht 0] at h
  simpa only [circleFlowLambda_localized_eq hε hG hperiod hab,
    circleFlowReferenceSize_localized_eq hε hG hperiod hab] using h

end ContinuousFlexibility.Analysis
