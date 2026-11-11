import ContinuousFlexibility.Analysis.OneHighCircleFlowReferenceIntegrability
import ContinuousFlexibility.Analysis.OneHighCircleFlowSpeedNorms
import ContinuousFlexibility.Analysis.OneHighCircleFourierRealAlgebra

/-!
# Actual norms of the speed relative to a scalar reference

The reference drops out of every positive angular derivative. In
particular its order-(s+1) difference norm controls the order-s norm
of the angular speed derivative. These are the quantities entering
the translation comparison, with their time integrability proved.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

abbrev circleFlowReferenceNorm (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (c : ℝ → ℝ) (s : ℕ) (t : ℝ) : ℝ :=
  circleRealSobolevNorm (s : ℝ)
    (circleSubtractConstantJet (circleFlowSpeedJet G hG hperiod t) (c t) 0)

def circleFlowReferenceSize (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (c : ℝ → ℝ) (s : ℕ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, circleFlowReferenceNorm G hG hperiod c s t

theorem intervalIntegrable_circleFlowReferenceNorm (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    {c : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : IntervalIntegrable c volume a b) (s : ℕ) :
    IntervalIntegrable (circleFlowReferenceNorm G hG hperiod c s) volume a b :=
  intervalIntegrable_circleSubtractConstantSobolevNorm (circleFlowSpeedJet G hG hperiod)
    hab (fun n => (continuous_circleFlowSpeedJet G hG hperiod n).continuousOn)
    (fun t _ => circleFlowSpeedJet_hasDerivAt G hG hperiod t) hc s

theorem circleFlowReferenceSize_nonneg (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (c : ℝ → ℝ) (s : ℕ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ circleFlowReferenceSize G hG hperiod c s a b :=
  intervalIntegral.integral_nonneg hab (fun _ _ => circle_real_sobolevNorm_nonneg _ _)

theorem circleFlowReferenceSize_partial_le (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    {c : ℝ → ℝ} {a b t : ℝ} (hc : IntervalIntegrable c volume a b)
    (ht : t ∈ Icc a b) (s : ℕ) :
    circleFlowReferenceSize G hG hperiod c s a t ≤
      circleFlowReferenceSize G hG hperiod c s a b := by
  have hI := intervalIntegrable_circleFlowReferenceNorm G hG hperiod (ht.1.trans ht.2) hc s
  have hat : IntervalIntegrable (circleFlowReferenceNorm G hG hperiod c s) volume a t := hI.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2)
  have htb : IntervalIntegrable (circleFlowReferenceNorm G hG hperiod c s) volume t b := hI.mono_set (by
    rw [uIcc_of_le ht.2, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc ht.1 le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hat htb
  have htail := circleFlowReferenceSize_nonneg G hG hperiod c s ht.2
  dsimp only [circleFlowReferenceSize] at htail ⊢
  linarith

/-- The actual derivative of the speed difference equals the angular
derivative of the speed, so no size of the reference enters this bound. -/
theorem circleFlowLambda_le_referenceSize (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    {c : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : IntervalIntegrable c volume a b) (s : ℕ) :
    circleFlowLambda G hG hperiod s a b ≤
      circleFlowReferenceSize G hG hperiod c (s + 1) a b := by
  apply intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_circleFlowSpeedSobolevNorm G hG hperiod s 1 a b)
    (intervalIntegrable_circleFlowReferenceNorm G hG hperiod hab hc (s + 1))
  intro t _
  have hh := circle_real_sobolevNorm_derivative_le
    (circleSubtractConstantJet (circleFlowSpeedJet G hG hperiod t) (c t))
    (circleSubtractConstantJet_hasDerivAt (circleFlowSpeedJet G hG hperiod t)
      (circleFlowSpeedJet_hasDerivAt G hG hperiod t) (c t)) s 1
  simpa [circleFlowReferenceNorm, circleSubtractConstantJet] using hh

end ContinuousFlexibility.Analysis
