import ContinuousFlexibility.Analysis.OneHighCircleFlowContinuity
import ContinuousFlexibility.Analysis.OneHighCircleFlowSpeedNorms

/-!
# Sobolev control of the genuine flow Jacobian

The exact exponential formula was derived from the classical trajectory
equation. Here the actual `H¹` norm of the speed's angular derivative
supplies its time-integrable envelope. No variational equation, joint
flow regularity, or frequency estimate is an additional premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

/-- A continuous pointwise speed envelope controls the actual angular
Jacobian throughout the original closed time interval. -/
theorem circleFlow_deriv_bounds {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {B : ℝ → ℝ} (hB : ContinuousOn B (Icc a b))
    (hbound : ∀ r ∈ Icc a b, ∀ η : ℝ, |angularPartial G (r, η)| ≤ B r)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    Real.exp (-(∫ r in a..b, B r)) ≤ deriv (fun η => Θ (t, η)) θ ∧
      deriv (fun η => Θ (t, η)) θ ≤ Real.exp (∫ r in a..b, B r) := by
  have hBat : IntervalIntegrable B volume a t :=
    (hB.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hBtb : IntervalIntegrable B volume t b :=
    (hB.mono (Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc ht.2
  have hκ : ContinuousOn (fun r => angularPartial G (r, Θ (r, θ))) (Icc a t) :=
    (contDiff_cylinder_angularPartial hG).continuous.comp_continuousOn
      (continuousOn_id.prodMk ((hΘ θ).mono (Icc_subset_Icc le_rfl ht.2)))
  have hmono : (∫ r in a..t, |angularPartial G (r, Θ (r, θ))|) ≤
      ∫ r in a..t, B r :=
    intervalIntegral.integral_mono_on (μ := volume) ht.1
      (hκ.abs.intervalIntegrable_of_Icc ht.1) hBat
      (fun r hr => hbound r ⟨hr.1, hr.2.trans ht.2⟩ _)
  have htail : 0 ≤ ∫ r in t..b, B r :=
    intervalIntegral.integral_nonneg ht.2
      (fun r hr => (abs_nonneg (angularPartial G (r, 0))).trans
        (hbound r ⟨ht.1.trans hr.1, hr.2⟩ 0))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hBat hBtb
  have htotal : |∫ r in a..t, angularPartial G (r, Θ (r, θ))| ≤
      ∫ r in a..b, B r := by
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := fun r => angularPartial G (r, Θ (r, θ))) ht.1
    linarith
  rw [(circleFlow_hasDerivAt_angle hG hP hperiod hΘ hinit hflow ht θ).deriv]
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp htotal).1,
    Real.exp_le_exp.mpr (abs_le.mp htotal).2⟩

variable {P : ℝ} [hP : Fact (0 < P)]

/-- The first assertion of the circle-flow lemma: the genuine Jacobian
lies between `exp (-C(P) Λ₁)` and `exp (C(P) Λ₁)`, uniformly in time and angle. -/
theorem circleFlow_deriv_bounds_sobolev {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    Real.exp (-(circleFlowEmbeddingConstant P * circleFlowLambda G hG hperiod 1 a b)) ≤
        deriv (fun η => Θ (t, η)) θ ∧
      deriv (fun η => Θ (t, η)) θ ≤
        Real.exp (circleFlowEmbeddingConstant P * circleFlowLambda G hG hperiod 1 a b) := by
  have hB : Continuous (fun r => circleFlowEmbeddingConstant P *
      circleRealSobolevNorm 1 (circleFlowSpeedJet G hG hperiod r 1)) := by
    apply continuous_const.mul
    simpa only [Nat.cast_one] using
      continuous_circleFlowSpeedSobolevNorm G hG hperiod 1 1
  have hbound := circleFlow_deriv_bounds hG hP.out hperiod hΘ hinit hflow
    hB.continuousOn (fun r _ η => circleFlow_angularSpeed_le_h1 G hG hperiod r η) ht θ
  simpa only [circleFlowLambda, Nat.cast_one, intervalIntegral.integral_const_mul] using hbound

end ContinuousFlexibility.Analysis
