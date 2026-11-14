module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowNormContinuity
public import ContinuousFlexibility.Analysis.CylinderMixedJets
public import ContinuousFlexibility.Analysis.CylinderSobolev

/-!
# Genuine speed norms and the integrated flow quantities

Every circle function below is the canonical descent of an actual
derivative of the given smooth periodic speed. Its Sobolev norm is
continuous in physical time and hence integrable on every compact time
interval. The pointwise estimate uses the existing physical-frequency
circle Sobolev embedding.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable {P : ℝ} [Fact (0 < P)]

/-- The canonical actual angular derivative tower of the speed at time `t`. -/
def circleFlowSpeedJet (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (t : ℝ) (n : ℕ) : C(AddCircle P, ℝ) :=
  periodicCircleJet (fun θ => G (t, θ)) (hperiod t)
    (hG.comp (contDiff_const.prodMk contDiff_id)) n

@[simp] theorem circleFlowSpeedJet_coe_apply (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (t : ℝ) (n : ℕ) (θ : ℝ) :
    circleFlowSpeedJet G hG hperiod t n (θ : AddCircle P) =
      iteratedDeriv n (fun η => G (t, η)) θ :=
  periodicCircleJet_coe_apply _ _ _ _ _

theorem circleFlowSpeedJet_hasDerivAt (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (t : ℝ) (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun η : ℝ => circleFlowSpeedJet G hG hperiod t n (η : AddCircle P))
      (circleFlowSpeedJet G hG hperiod t (n + 1) (θ : AddCircle P)) θ :=
  periodicCircleJet_hasDerivAt _ _ _ _ _

theorem continuous_circleFlowSpeedJet (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P) (n : ℕ) :
    Continuous (fun t => circleFlowSpeedJet G hG hperiod t n) := by
  apply continuous_periodicCircleJet_family
  have hc := (contDiffOn_univ.mp
    (Statements.contDiffOn_mixedDerivative isOpen_univ hG.contDiffOn 0 n)).continuous
  exact hc.congr (fun p => by simp only [Statements.mixedDerivative, iteratedDeriv_zero])

/-- All actual speed-derivative Sobolev norms are continuous in time. -/
theorem continuous_circleFlowSpeedSobolevNorm (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P) (s k : ℕ) :
    Continuous (fun t => circleRealSobolevNorm (s : ℝ) (circleFlowSpeedJet G hG hperiod t k)) := by
  have hd (t : ℝ) (j : ℕ) (θ : ℝ) :
      HasDerivAt (fun η : ℝ =>
        circleFlowSpeedJet G hG hperiod t (k + j) (η : AddCircle P))
        (circleFlowSpeedJet G hG hperiod t (k + (j + 1)) (θ : AddCircle P)) θ := by
    simpa only [Nat.add_assoc] using circleFlowSpeedJet_hasDerivAt G hG hperiod t (k + j) θ
  simpa only [Nat.add_zero] using continuous_circleRealSobolevNorm_of_derivatives
    (fun t j => circleFlowSpeedJet G hG hperiod t (k + j)) hd s
    (by simpa only [Nat.add_zero] using continuous_circleFlowSpeedJet G hG hperiod k)
    (continuous_circleFlowSpeedJet G hG hperiod (k + s))

theorem intervalIntegrable_circleFlowSpeedSobolevNorm (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (s k : ℕ) (a b : ℝ) :
    IntervalIntegrable
      (fun t => circleRealSobolevNorm (s : ℝ) (circleFlowSpeedJet G hG hperiod t k))
      volume a b :=
  (continuous_circleFlowSpeedSobolevNorm G hG hperiod s k).intervalIntegrable a b

/-- The manuscript's `Λ_s`, formed from the actual first angular derivative. -/
def circleFlowLambda (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (s : ℕ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (circleFlowSpeedJet G hG hperiod t 1)

theorem circleFlowLambda_nonneg (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (s : ℕ) {a b : ℝ} (hab : a ≤ b) : 0 ≤ circleFlowLambda G hG hperiod s a b :=
  intervalIntegral.integral_nonneg hab (fun _ _ => ENNReal.toReal_nonneg)

/-- A strictly positive embedding constant depending only on the period. -/
def circleFlowEmbeddingConstant (P : ℝ) : ℝ :=
  1 + (eLpNorm (fun n : ℤ => circleFrequencyWeight P n ^ (-1 : ℝ)) 2 Measure.count).toReal

theorem circleFlowEmbeddingConstant_pos (P : ℝ) : 0 < circleFlowEmbeddingConstant P := by
  dsimp only [circleFlowEmbeddingConstant]
  positivity

/-- The actual angular derivative is controlled pointwise by its physical
`H¹` norm; all required Fourier finiteness follows from smoothness. -/
theorem circleFlow_angularSpeed_le_h1 (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P) (t θ : ℝ) :
    |angularPartial G (t, θ)| ≤ circleFlowEmbeddingConstant P *
      circleRealSobolevNorm 1 (circleFlowSpeedJet G hG hperiod t 1) := by
  have hfinite := circle_frequencyWeighted_memLp_of_derivatives_at
    (fun k => circleComplexify (circleFlowSpeedJet G hG hperiod t k))
    (circleComplexify_hasDerivAt (circleFlowSpeedJet G hG hperiod t)
      (circleFlowSpeedJet_hasDerivAt G hG hperiod t)) 1 1
  have hh := circle_norm_apply_le_h1
    (circleComplexify (circleFlowSpeedJet G hG hperiod t 1))
    (by simpa only [Nat.cast_one] using hfinite) (θ : AddCircle P)
  have hbase : |angularPartial G (t, θ)| ≤
      (eLpNorm (fun n : ℤ => circleFrequencyWeight P n ^ (-1 : ℝ)) 2 Measure.count).toReal *
      circleRealSobolevNorm 1 (circleFlowSpeedJet G hG hperiod t 1) := by
    simpa only [circleComplexify_apply, circleFlowSpeedJet_coe_apply, iteratedDeriv_one,
      Complex.norm_real, Real.norm_eq_abs,
      deriv_cylinder_angular_slice (hG.differentiable (by simp))] using hh
  apply hbase.trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  dsimp only [circleFlowEmbeddingConstant]
  linarith

end ContinuousFlexibility.Analysis
