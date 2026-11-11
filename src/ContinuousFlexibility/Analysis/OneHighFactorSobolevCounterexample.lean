import ContinuousFlexibility.Analysis.OneHighFactorCounterexample
import ContinuousFlexibility.Analysis.OneHighCircleSobolevAlgebra
import ContinuousFlexibility.Analysis.OneHighCircleRealSobolev

/-!
# The composition obstruction in the actual physical Sobolev norms

The constant-input counterexamples use the same normalized Haar measure,
actual Fourier coefficients, and Bessel Sobolev norms as the positive
composition theorems. They refute the original uniform dependence at H¹
and its derivative-free order-zero version.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

theorem oneHighFactor_circleConstant_sobolevNorm (s c : ℝ) :
    circleRealSobolevNorm s (ContinuousMap.const (AddCircle P) c) = |c| := by
  have hfun :
      (circleComplexify (ContinuousMap.const (AddCircle P) c) : AddCircle P → ℂ) =
        (fun _ : AddCircle P => (c : ℂ)) := by
    funext θ
    simp only [circleComplexify_apply, ContinuousMap.const_apply]
  change circleSobolevNorm s
    (circleComplexify (ContinuousMap.const (AddCircle P) c)) = |c|
  rw [hfun, circle_sobolevNorm_const, Complex.norm_real, Real.norm_eq_abs]

/-- The original range-only derivative dependence fails in the actual H¹
norm, with the fixed smooth input one and derivative bound zero on its range. -/
theorem oneHighFactor_no_range_only_circle_h1_bound :
    ¬ ∃ C : ℝ, ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → Φ 0 = 0 → deriv Φ 1 = 0 →
      circleRealSobolevNorm 1
        (ContinuousMap.const (AddCircle P) (Φ 1 - Φ 0)) ≤
        C * circleRealSobolevNorm 1 (ContinuousMap.const (AddCircle P) (1 : ℝ)) := by
  rintro ⟨C, hC⟩
  apply oneHighFactor_no_range_only_composition_bound
  refine ⟨C, ?_⟩
  intro Φ hΦ hzero hderiv
  have h := hC Φ hΦ hzero hderiv
  simpa only [oneHighFactor_circleConstant_sobolevNorm, abs_one, mul_one] using h

/-- At order zero the same actual Sobolev norm still requires
first-derivative control along the segment to the base point. -/
theorem oneHighFactor_no_derivative_free_circle_h0_bound :
    ¬ ∃ C : ℝ, ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → Φ 0 = 0 →
      circleRealSobolevNorm 0
        (ContinuousMap.const (AddCircle P) (Φ 1 - Φ 0)) ≤
        C * circleRealSobolevNorm 0 (ContinuousMap.const (AddCircle P) (1 : ℝ)) := by
  rintro ⟨C, hC⟩
  apply oneHighFactor_no_derivative_free_composition_bound
  refine ⟨C, ?_⟩
  intro Φ hΦ hzero
  have h := hC Φ hΦ hzero
  simpa only [oneHighFactor_circleConstant_sobolevNorm, abs_one, mul_one] using h

end ContinuousFlexibility.Analysis
