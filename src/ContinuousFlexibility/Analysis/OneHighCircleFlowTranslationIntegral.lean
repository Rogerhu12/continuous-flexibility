module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowTranslationFamilies

/-!
# The genuine integral equation for translation displacement

The equation for every angular jet is integrated in physical time.
Subtracting an integrable scalar reference changes only the zeroth jet.
The resulting Sobolev integral inequality therefore follows from the
actual flow equation for arbitrary integrable reference speeds.
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

theorem circleFlowDisplacementJet_integral_eq {t : ℝ} (ht : t ∈ Icc a b)
    (n : ℕ) (x : AddCircle P) :
    circleFlowDisplacementJet hG hperiod hΘ hinit hflow t n x =
      ∫ r in a..t, circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r n x := by
  induction x using QuotientAddGroup.induction_on
  rename_i θ
  have hint : (∫ r in a..t,
      circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r n (θ : AddCircle P)) =
      ∫ r in a..t, iteratedDeriv n (fun η => G (r, Θ (r, η))) θ := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by
      have hh : r ∈ Icc a t := by simpa only [uIcc_of_le ht.1] using hr
      exact ⟨hh.1, hh.2.trans ht.2⟩
    exact circleFlowComposedSpeedJet_coe_apply hG hperiod hΘ hinit hflow hr' n θ
  rw [circleFlowDisplacementJet_coe_apply hG hperiod hΘ hinit hflow ht n θ, hint]
  have hi := circleFlow_angularJet_integral_eq hG hP.out hperiod hΘ hinit hflow n ht θ
  linarith

theorem circleFlowTranslationJet_integral_eq {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) {t : ℝ} (ht : t ∈ Icc a b)
    (n : ℕ) (x : AddCircle P) :
    circleFlowTranslationJet hG hperiod hΘ hinit hflow c t n x =
      ∫ r in a..t,
        circleSubtractConstantJet (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r)
          (c r) n x := by
  have hc' : IntervalIntegrable c volume a t := hc.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2)
  have hf : IntervalIntegrable
      (fun r => circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r n) volume a t :=
    ((continuousOn_circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow n).mono
      (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  let ev : C(AddCircle P, ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ x
  have hev : IntervalIntegrable
      (fun r => ev (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r n)) volume a t :=
    ⟨ev.integrable_comp hf.1, ev.integrable_comp hf.2⟩
  have hfe : IntervalIntegrable
      (fun r => circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r n x) volume a t := by
    simpa only [ev, ContinuousMap.evalCLM_apply] using hev
  have hbase := circleFlowDisplacementJet_integral_eq hG hperiod hΘ hinit hflow ht n x
  simp only [circleFlowTranslationJet, circleSubtractConstantJet_apply]
  by_cases hn : n = 0
  · simp only [if_pos hn]
    rw [hbase, intervalIntegral.integral_sub hfe hc']
  · simpa only [if_neg hn, sub_zero] using hbase

/-- Sobolev control of the actual displacement from the reference
translation, before applying the already proved composition bounds. -/
theorem circleFlow_translation_sobolev_integral_le {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ)
        (circleFlowTranslationJet hG hperiod hΘ hinit hflow c t 0) ≤
      (2 : ℝ) ^ (s + 1) * ∫ r in a..t, circleRealSobolevNorm (s : ℝ)
        (circleSubtractConstantJet (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r)
          (c r) 0) := by
  have hc' : IntervalIntegrable c volume a t := hc.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2)
  have hfamily (n : ℕ) : ContinuousOn
      (fun r => circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r n) (Icc a t) :=
    (continuousOn_circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow n).mono
      (Icc_subset_Icc le_rfl ht.2)
  have hderiv (r : ℝ) (hr : r ∈ Icc a t) (n : ℕ) (θ : ℝ) :
      HasDerivAt (fun η : ℝ =>
        circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r n (η : AddCircle P))
        (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r (n + 1) (θ : AddCircle P)) θ :=
    circleFlowComposedSpeedJet_hasDerivAt hG hperiod hΘ hinit hflow
      ⟨hr.1, hr.2.trans ht.2⟩ n θ
  exact circle_real_sobolevNorm_intervalIntegral_le_of_integrable
    (circleFlowTranslationJet hG hperiod hΘ hinit hflow c t)
    (fun r => circleSubtractConstantJet
      (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r) (c r)) ht.1
    (circleFlowTranslationJet_hasDerivAt hG hperiod hΘ hinit hflow c ht)
    (fun r hr => circleSubtractConstantJet_hasDerivAt
      (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow r) (hderiv r hr) (c r))
    (intervalIntegrable_circleSubtractConstantJet
      (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow) ht.1 hfamily hc')
    (circleFlowTranslationJet_integral_eq hG hperiod hΘ hinit hflow hc ht) s
    (intervalIntegrable_circleSubtractConstantSobolevNorm
      (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow) ht.1 hfamily hderiv hc' s)

end ContinuousFlexibility.Analysis
