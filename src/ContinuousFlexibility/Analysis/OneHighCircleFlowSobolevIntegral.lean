module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowCircleFamilies

/-!
# The true flow equation in physical Sobolev norm

The integral equation for each actual angular jet descends to its
canonical circle representative. The proven Minkowski bound then gives
the Sobolev integral inequality for the derivative defect itself.
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

/-- The canonical defect jets satisfy the actual time integral equation
on the circle, including its initial and terminal times. -/
theorem circleFlowDefectJet_integral_eq {t : ℝ} (ht : t ∈ Icc a b)
    (n : ℕ) (x : AddCircle P) :
    circleFlowDefectJet hG hperiod hΘ hinit hflow t n x =
      ∫ r in a..t, circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r (n + 1) x := by
  induction x using QuotientAddGroup.induction_on
  rename_i θ
  have hint : (∫ r in a..t,
      circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r (n + 1) (θ : AddCircle P)) =
      ∫ r in a..t, iteratedDeriv (n + 1) (fun η => G (r, Θ (r, η))) θ := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by
      have hh : r ∈ Icc a t := by simpa only [uIcc_of_le ht.1] using hr
      exact ⟨hh.1, hh.2.trans ht.2⟩
    exact circleFlowComposedSpeedJet_coe_apply hG hperiod hΘ hinit hflow hr' (n + 1) θ
  rw [circleFlowDefectJet_coe_apply hG hperiod hΘ hinit hflow ht n θ, hint]
  have hi := circleFlow_angularJet_integral_eq hG hP.out hperiod hΘ hinit hflow (n + 1) ht θ
  have hid : iteratedDeriv (n + 1) (id : ℝ → ℝ) θ = if n = 0 then 1 else 0 := by
    rw [iteratedDeriv_id, if_neg (Nat.succ_ne_zero n)]
    by_cases hn : n = 0
    · subst n
      norm_num
    · rw [if_neg (by omega : n + 1 ≠ 1), if_neg hn]
  rw [hid] at hi
  linarith

/-- The Sobolev integral inequality follows from the supplied classical
flow equation, not from an assumed norm differential inequality. -/
theorem circleFlow_defect_sobolev_integral_le (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ) (circleFlowDefectJet hG hperiod hΘ hinit hflow t 0) ≤
      (2 : ℝ) ^ (s + 1) * ∫ r in a..t,
        circleRealSobolevNorm (s : ℝ) (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r 1) := by
  exact circle_real_sobolevNorm_intervalIntegral_le
    (circleFlowDefectJet hG hperiod hΘ hinit hflow t)
    (fun r n => circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r (n + 1)) ht.1
    (circleFlowDefectJet_hasDerivAt hG hperiod hΘ hinit hflow ht)
    (fun r hr n θ => circleFlowComposedSpeedJet_hasDerivAt hG hperiod hΘ hinit hflow
      ⟨hr.1, hr.2.trans ht.2⟩ (n + 1) θ)
    (fun n => (continuousOn_circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow (n + 1)).mono
      (Icc_subset_Icc le_rfl ht.2))
    (circleFlowDefectJet_integral_eq hG hperiod hΘ hinit hflow ht) s

end ContinuousFlexibility.Analysis
