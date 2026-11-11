import ContinuousFlexibility.Analysis.OneHighCircleFlowSmooth
import ContinuousFlexibility.Analysis.OneHighCircleFlowContinuity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.IntermediateValue

/-!
# Smooth time changes of the supplied compact-interval flow

A smooth time change stays inside the original closed time interval.
The fundamental theorem of calculus proves its scaled ODE, including at
times mapped to either endpoint. The resulting global family is therefore
smooth by the global bootstrap. A flat transition reaching every time in
the original interval proves actual angular smoothness at every slice,
including both endpoint slices, without extending the supplied solution.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The ODE of a time-changed trajectory follows from its integral
equation, so the original ODE is only required in the open interval. -/
theorem hasDerivAt_timeChange_classicalTrajectory {G : PolarPoint → ℝ}
    {u τ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hG : Continuous G)
    (hu : ContinuousOn u (Icc a b))
    (hdu : ∀ r ∈ Ioo a b, HasDerivAt u (G (r, u r)) r)
    (hτrange : ∀ s : ℝ, τ s ∈ Icc a b) {s d : ℝ} (hτ : HasDerivAt τ d s) :
    HasDerivAt (fun r => u (τ r)) (d * G (τ s, u (τ s))) s := by
  let clamp : ℝ → ℝ := fun r => max a (min r b)
  have hc : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  have hmem (r : ℝ) : clamp r ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have heq (r : ℝ) (hr : r ∈ Icc a b) : clamp r = r := by
    dsimp only [clamp]
    rw [min_eq_left hr.2, max_eq_right hr.1]
  let κ : ℝ → ℝ := fun r => G (clamp r, u (clamp r))
  have hκ : Continuous κ := hG.comp (hc.prodMk (hu.comp_continuous hc hmem))
  have hκeq (r : ℝ) (hr : r ∈ Icc a b) : κ r = G (r, u r) := by
    dsimp only [κ]
    rw [heq r hr]
  have hprimitive (r : ℝ) (hr : r ∈ Icc a b) :
      u r = u a + ∫ q in a..r, κ q := by
    have hd (q : ℝ) (hq : q ∈ Ioo a r) : HasDerivAt u (κ q) q := by
      rw [hκeq q ⟨hq.1.le, hq.2.le.trans hr.2⟩]
      exact hdu q ⟨hq.1, hq.2.trans_le hr.2⟩
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1
      (hu.mono (Icc_subset_Icc le_rfl hr.2)) hd (hκ.intervalIntegrable a r)
    linarith
  have hcompose : (fun r => u (τ r)) = fun r => u a + ∫ q in a..τ r, κ q :=
    funext (fun r => hprimitive (τ r) (hτrange r))
  have hd : HasDerivAt (fun r => u a + ∫ q in a..τ r, κ q) (κ (τ s) * d) s :=
    (((hκ.integral_hasStrictDerivAt a (τ s)).hasDerivAt).comp s hτ).const_add (u a)
  rw [← hcompose] at hd
  apply hd.congr_deriv
  rw [hκeq (τ s) (hτrange s)]
  ring

/-- Every smooth time change of the supplied flow, starting at its
initial time and staying in its original interval, is jointly smooth. -/
theorem contDiff_circleFlow_timeChange {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (hτzero : τ 0 = a)
    (hτrange : ∀ s : ℝ, τ s ∈ Icc a b) :
    ContDiff ℝ ∞ (fun p : PolarPoint => Θ (τ p.1, p.2)) := by
  let V : PolarPoint → ℝ := fun p => deriv τ p.1 * G (τ p.1, p.2)
  have hV : ContDiff ℝ ∞ V :=
    ((contDiff_infty_iff_deriv.mp hτ).2.comp contDiff_fst).mul
      (hG.comp ((hτ.comp contDiff_fst).prodMk contDiff_snd))
  have hcontinuous : Continuous (fun p : PolarPoint => Θ (τ p.1, p.2)) :=
    (circleFlow_continuousOn hG hP hperiod hΘ hinit hflow).comp_continuous
      ((hτ.continuous.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨hτrange p.1, mem_univ p.2⟩)
  have hinitial (θ : ℝ) : Θ (τ 0, θ) = θ := by rw [hτzero, hinit θ]
  have htime (t θ : ℝ) : HasDerivAt (fun r => Θ (τ r, θ))
      (V (t, Θ (τ t, θ))) t :=
    hasDerivAt_timeChange_classicalTrajectory ((hτrange 0).1.trans (hτrange 0).2)
      hG.continuous (hΘ θ) (fun r hr => hflow r hr θ) hτrange
      ((hτ.differentiable (by simp) t).hasDerivAt)
  exact contDiff_globalCircleFlow hV hcontinuous hinitial htime

/-- A flat smooth map from real time onto the supplied compact interval. -/
def circleFlowCompactTime (a b s : ℝ) : ℝ :=
  a + (b - a) * Real.smoothTransition s

theorem contDiff_circleFlowCompactTime (a b : ℝ) : ContDiff ℝ ∞ (circleFlowCompactTime a b) :=
  contDiff_const.add (contDiff_const.mul Real.smoothTransition.contDiff)

theorem circleFlowCompactTime_zero (a b : ℝ) : circleFlowCompactTime a b 0 = a := by
  simp only [circleFlowCompactTime, Real.smoothTransition.zero, mul_zero, add_zero]

theorem circleFlowCompactTime_one (a b : ℝ) : circleFlowCompactTime a b 1 = b := by
  simp only [circleFlowCompactTime, Real.smoothTransition.one, mul_one]
  ring

theorem circleFlowCompactTime_mem {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    circleFlowCompactTime a b s ∈ Icc a b := by
  have hlo := mul_nonneg (sub_nonneg.mpr hab) (Real.smoothTransition.nonneg s)
  have hhi := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one s) (sub_nonneg.mpr hab)
  constructor <;> dsimp only [circleFlowCompactTime] <;> linarith

theorem circleFlowCompactTime_surjOn (a b : ℝ) :
    SurjOn (circleFlowCompactTime a b) (Icc (0 : ℝ) 1) (Icc a b) := by
  intro t ht
  apply intermediate_value_Icc zero_le_one (contDiff_circleFlowCompactTime a b).continuous.continuousOn
  simpa only [circleFlowCompactTime_zero, circleFlowCompactTime_one] using ht

/-- Each actual time slice of the supplied classical periodic flow is
smooth in its initial angle, including the two endpoint slices. -/
theorem circleFlow_contDiff_angle {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (fun θ => Θ (t, θ)) := by
  have hsmooth := contDiff_circleFlow_timeChange hG hP hperiod hΘ hinit hflow
    (contDiff_circleFlowCompactTime a b) (circleFlowCompactTime_zero a b)
    (circleFlowCompactTime_mem (ht.1.trans ht.2))
  obtain ⟨s, _, hs⟩ := circleFlowCompactTime_surjOn a b ht
  have hslice : ContDiff ℝ ∞ (fun θ => Θ (circleFlowCompactTime a b s, θ)) :=
    hsmooth.comp (contDiff_const.prodMk contDiff_id)
  simpa only [hs] using hslice

end ContinuousFlexibility.Analysis
