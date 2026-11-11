import ContinuousFlexibility.Analysis.OneHighCircleFlowJacobian
import ContinuousFlexibility.Analysis.OneHighCircleSobolevAlgebra

/-!
# The common low Sobolev envelope for circle flows

The physical `H⁴` norm of the angular speed derivative bounds all speed
derivatives of orders one through four. Monotonicity also replaces the
`Λ₁` in the Jacobian bounds by `Λ₄`. Thus all the low geometry data needed
by circle composition depend on the same integrated quantity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable {P : ℝ} [hP : Fact (0 < P)]

theorem circleFlow_speedDerivative_le_h4 (G : PolarPoint → ℝ)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (t : ℝ) {j : ℕ} (hj : 1 ≤ j) (hj4 : j ≤ 4) (θ : ℝ) :
    |iteratedDeriv j (fun η => G (t, η)) θ| ≤ circleSobolevEmbeddingConstant P *
      circleRealSobolevNorm 4 (circleFlowSpeedJet G hG hperiod t 1) := by
  let f : ℕ → C(AddCircle P, ℝ) := fun k => circleFlowSpeedJet G hG hperiod t (k + 1)
  have hd (k : ℕ) (x : ℝ) :
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P)) (f (k + 1) (x : AddCircle P)) x :=
    circleFlowSpeedJet_hasDerivAt G hG hperiod t (k + 1) x
  have hindex : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have horder : 1 + (j - 1) = j := by omega
  have hshift : circleRealSobolevNorm 1 (f (j - 1)) ≤
      circleRealSobolevNorm (j : ℝ) (f 0) := by
    simpa only [Nat.cast_one, horder] using circle_sobolevNorm_derivative_le
      (fun k => circleComplexify (f k)) (circleComplexify_hasDerivAt f hd) 1 (j - 1)
  have hmono : circleRealSobolevNorm (j : ℝ) (f 0) ≤ circleRealSobolevNorm 4 (f 0) :=
    circle_sobolevNorm_mono_of_derivatives
      (fun k => circleComplexify (f k)) (circleComplexify_hasDerivAt f hd) hj4
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  calc
    |iteratedDeriv j (fun η => G (t, η)) θ| =
        ‖circleComplexify (f (j - 1)) (θ : AddCircle P)‖ := by
      simp only [f, circleComplexify_apply, circleFlowSpeedJet_coe_apply, hindex,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖circleComplexify (f (j - 1))‖ := (circleComplexify (f (j - 1))).norm_coe_le_norm _
    _ ≤ circleSobolevEmbeddingConstant P * circleRealSobolevNorm 1 (f (j - 1)) :=
      circle_supNorm_le_sobolev_one_of_derivatives
        (fun k => circleComplexify (f k)) (circleComplexify_hasDerivAt f hd) (j - 1)
    _ ≤ circleSobolevEmbeddingConstant P * circleRealSobolevNorm 4 (f 0) :=
      mul_le_mul_of_nonneg_left (hshift.trans hmono) hE
    _ = _ := rfl

/-- Monotonicity of the integrated actual speed-derivative norms. -/
theorem circleFlowLambda_mono (G : PolarPoint → ℝ) (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    {s k : ℕ} (hsk : s ≤ k) {a b : ℝ} (hab : a ≤ b) :
    circleFlowLambda G hG hperiod s a b ≤ circleFlowLambda G hG hperiod k a b := by
  apply intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_circleFlowSpeedSobolevNorm G hG hperiod s 1 a b)
    (intervalIntegrable_circleFlowSpeedSobolevNorm G hG hperiod k 1 a b)
  intro t _
  let f : ℕ → C(AddCircle P, ℝ) := fun j => circleFlowSpeedJet G hG hperiod t (j + 1)
  have hd (j : ℕ) (x : ℝ) :
      HasDerivAt (fun y : ℝ => f j (y : AddCircle P)) (f (j + 1) (x : AddCircle P)) x :=
    circleFlowSpeedJet_hasDerivAt G hG hperiod t (j + 1) x
  exact circle_sobolevNorm_mono_of_derivatives
    (fun j => circleComplexify (f j)) (circleComplexify_hasDerivAt f hd) hsk

/-- Both Jacobian bounds use only `Λ₄`, as required by the tame constants. -/
theorem circleFlow_deriv_bounds_lowSobolev {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    Real.exp (-(circleFlowEmbeddingConstant P * circleFlowLambda G hG hperiod 4 a b)) ≤
        deriv (fun η => Θ (t, η)) θ ∧
      deriv (fun η => Θ (t, η)) θ ≤
        Real.exp (circleFlowEmbeddingConstant P * circleFlowLambda G hG hperiod 4 a b) := by
  have hbase := circleFlow_deriv_bounds_sobolev hG hperiod hΘ hinit hflow ht θ
  have hcoef := mul_le_mul_of_nonneg_left
    (circleFlowLambda_mono G hG hperiod (by norm_num : (1 : ℕ) ≤ 4) (ht.1.trans ht.2))
    (circleFlowEmbeddingConstant_pos P).le
  exact ⟨(Real.exp_le_exp.mpr (neg_le_neg hcoef)).trans hbase.1,
    hbase.2.trans (Real.exp_le_exp.mpr hcoef)⟩

end ContinuousFlexibility.Analysis
