import ContinuousFlexibility.Analysis.OneHighCircleFlowSourceEstimate
import ContinuousFlexibility.Analysis.OneHighCircleFlowSobolevIntegral
import ContinuousFlexibility.Analysis.OneHighCircleFlowLowGeometry

/-!
# Genuine high Sobolev bounds for the circle flow

The actual jet integral equation, the proved Sobolev Minkowski bound,
and the actual composition estimate give the variable-coefficient
Gronwall inequality. Both low geometric inputs to composition have
already been derived from the same integrated speed norm. Consequently
the final constant depends only on the period, the order, and Λ₄.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

def circleFlowSobolevConstant (P L : ℝ) (s : ℕ) : ℝ :=
  let K : ℝ := (2 : ℝ) ^ (s + 1) *
    circleFlowSourceConstant P (Real.exp (-(circleFlowEmbeddingConstant P * L)))
      (circleFlowLowGeometryBound P L) s
  K * Real.exp (K * L)

theorem circleFlowSobolevConstant_pos (P L : ℝ) (s : ℕ) :
    0 < circleFlowSobolevConstant P L s := by
  have hC : 0 < circleFlowSourceConstant P
      (Real.exp (-(circleFlowEmbeddingConstant P * L))) (circleFlowLowGeometryBound P L) s :=
    lt_of_lt_of_le zero_lt_one (circleFlowSourceConstant_one_le _ _ _ _)
  dsimp only [circleFlowSobolevConstant]
  positivity

variable {P : ℝ} [hP : Fact (0 < P)]
  {G Θ : PolarPoint → ℝ} {a b : ℝ}
  (hG : ContDiff ℝ ∞ G)
  (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
  (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
  (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
  (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
    HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)

/-- The source estimate has only genuine flow and speed hypotheses;
both of its circle geometry bounds have been proved from Λ₄. -/
theorem circleFlow_source_sobolev_le (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ)
        (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t 1) ≤
      circleFlowSourceConstant P
        (Real.exp (-(circleFlowEmbeddingConstant P * circleFlowLambda G hG hperiod 4 a b)))
        (circleFlowLowGeometryBound P (circleFlowLambda G hG hperiod 4 a b)) s *
        (circleRealSobolevNorm (s : ℝ) (circleFlowSpeedJet G hG hperiod t 1) +
          circleRealSobolevNorm 3 (circleFlowSpeedJet G hG hperiod t 1) *
            circleRealSobolevNorm (s : ℝ)
              (circleFlowDefectJet hG hperiod hΘ hinit hflow t 0)) := by
  have hL := circleFlowLambda_nonneg G hG hperiod 4 (ht.1.trans ht.2)
  rw [circleFlowComposedSpeedJet_eq hG hperiod hΘ hinit hflow ht 1,
    circleFlowDefectJet_eq hG hperiod hΘ hinit hflow ht 0]
  exact circleLift_composed_derivative_sobolev_le s
    (fun θ => G (t, θ)) (hperiod t) (hG.comp (contDiff_const.prodMk contDiff_id))
    (fun θ => Θ (t, θ))
    (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)
    (circleFlow_lift_add hG hperiod hΘ hinit hflow ht)
    (Real.exp_pos _) (circleFlowLowGeometryBound_nonneg P hL)
    (fun θ => (circleFlow_deriv_bounds_lowSobolev hG hperiod hΘ hinit hflow ht θ).1)
    (circleFlow_defect_h3_le hG hperiod hΘ hinit hflow ht)

private theorem circleFlow_continuousOn_sourceSobolevNorm (s : ℕ) :
    ContinuousOn (fun t => circleRealSobolevNorm (s : ℝ)
      (circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t 1)) (Icc a b) := by
  exact continuousOn_circleRealSobolevNorm_of_derivatives
    (fun t n => circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow t (n + 1))
    (fun t ht n θ =>
      circleFlowComposedSpeedJet_hasDerivAt hG hperiod hΘ hinit hflow ht (n + 1) θ) s
    (continuousOn_circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow 1)
    (continuousOn_circleFlowComposedSpeedJet hG hperiod hΘ hinit hflow (s + 1))

/-- The full high Sobolev estimate for the derivative defect of the
supplied classical circle flow, uniformly on the closed time interval. -/
theorem circleFlow_defect_sobolev_le (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ) (circleFlowDefectJet hG hperiod hΘ hinit hflow t 0) ≤
      circleFlowSobolevConstant P (circleFlowLambda G hG hperiod 4 a b) s *
        circleFlowLambda G hG hperiod s a b := by
  let L : ℝ := circleFlowLambda G hG hperiod 4 a b
  let C : ℝ := circleFlowSourceConstant P
    (Real.exp (-(circleFlowEmbeddingConstant P * L))) (circleFlowLowGeometryBound P L) s
  let K : ℝ := (2 : ℝ) ^ (s + 1) * C
  let u : ℝ → ℝ := fun r => circleRealSobolevNorm (s : ℝ)
    (circleFlowDefectJet hG hperiod hΘ hinit hflow r 0)
  let A : ℕ → ℝ → ℝ := fun k r =>
    circleRealSobolevNorm (k : ℝ) (circleFlowSpeedJet G hG hperiod r 1)
  have hC : 0 ≤ C := zero_le_one.trans (circleFlowSourceConstant_one_le _ _ _ _)
  have hK : 0 ≤ K := mul_nonneg (by positivity) hC
  have hu : ContinuousOn u (Icc a b) :=
    continuousOn_circleFlowDefectSobolevNorm hG hperiod hΘ hinit hflow s
  have hA (k : ℕ) : Continuous (A k) :=
    continuous_circleFlowSpeedSobolevNorm G hG hperiod k 1
  have hAn (k : ℕ) (r : ℝ) : 0 ≤ A k r := circle_real_sobolevNorm_nonneg _ _
  have hsource := circleFlow_continuousOn_sourceSobolevNorm hG hperiod hΘ hinit hflow s
  have hright : ContinuousOn (fun r => C * (A s r + A 3 r * u r)) (Icc a b) :=
    continuousOn_const.mul ((hA s).continuousOn.add ((hA 3).continuousOn.mul hu))
  have hlin (τ : ℝ) (hτ : τ ∈ Icc a t) :
      u τ ≤ 0 + ∫ r in a..τ, (K * A 3 r) * u r + K * A s r := by
    have hτab : τ ∈ Icc a b := ⟨hτ.1, hτ.2.trans ht.2⟩
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hτ.1
      ((hsource.mono (Icc_subset_Icc le_rfl hτab.2)).intervalIntegrable_of_Icc hτ.1)
      ((hright.mono (Icc_subset_Icc le_rfl hτab.2)).intervalIntegrable_of_Icc hτ.1)
      (fun r hr => circleFlow_source_sobolev_le hG hperiod hΘ hinit hflow s
        ⟨hr.1, hr.2.trans hτab.2⟩)
    have hraw : u τ ≤ (2 : ℝ) ^ (s + 1) *
        (C * ∫ r in a..τ, A s r + A 3 r * u r) := by
      apply (circleFlow_defect_sobolev_integral_le hG hperiod hΘ hinit hflow s hτab).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [intervalIntegral.integral_const_mul] using hmono
    have heq : (∫ r in a..τ, (K * A 3 r) * u r + K * A s r) =
        K * ∫ r in a..τ, A s r + A 3 r * u r := by
      calc
        _ = ∫ r in a..τ, K * (A s r + A 3 r * u r) := by
          apply intervalIntegral.integral_congr
          intro r _
          ring
        _ = _ := intervalIntegral.integral_const_mul _ _
    rw [zero_add, heq]
    simpa only [K, mul_assoc] using hraw
  have hgronwall := integral_gronwall_of_continuousOn ht.1
    (hu.mono (Icc_subset_Icc le_rfl ht.2))
    ((continuous_const.mul (hA 3)).continuousOn.mono (Icc_subset_Icc le_rfl ht.2))
    ((continuous_const.mul (hA s)).continuousOn.mono (Icc_subset_Icc le_rfl ht.2))
    (fun r _ => mul_nonneg hK (hAn 3 r))
    (fun r _ => mul_nonneg hK (hAn s r)) hlin
  have hshort (k : ℕ) : (∫ r in a..t, A k r) ≤ circleFlowLambda G hG hperiod k a b := by
    have hat : IntervalIntegrable (A k) volume a t := (hA k).intervalIntegrable a t
    have htb : IntervalIntegrable (A k) volume t b := (hA k).intervalIntegrable t b
    have hadd := intervalIntegral.integral_add_adjacent_intervals hat htb
    have htail : 0 ≤ ∫ r in t..b, A k r :=
      intervalIntegral.integral_nonneg (μ := volume) ht.2 (fun r _ => hAn k r)
    dsimp only [A, circleFlowLambda] at hadd htail ⊢
    linarith
  have hthree : (∫ r in a..t, A 3 r) ≤ L :=
    (hshort 3).trans (circleFlowLambda_mono G hG hperiod
      (by norm_num : (3 : ℕ) ≤ 4) (ht.1.trans ht.2))
  have hexp : Real.exp (K * ∫ r in a..t, A 3 r) ≤ Real.exp (K * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hthree hK)
  calc
    u t ≤ (K * ∫ r in a..t, A s r) * Real.exp (K * ∫ r in a..t, A 3 r) := by
      simpa only [zero_add, Pi.mul_def, Pi.mul_apply, K, intervalIntegral.integral_const_mul] using hgronwall
    _ ≤ (K * circleFlowLambda G hG hperiod s a b) * Real.exp (K * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hshort s) hK) hexp (Real.exp_pos _).le
        (mul_nonneg hK (circleFlowLambda_nonneg G hG hperiod s (ht.1.trans ht.2)))
    _ = _ := by
      dsimp only [circleFlowSobolevConstant, K, C, L]
      ring

end ContinuousFlexibility.Analysis
