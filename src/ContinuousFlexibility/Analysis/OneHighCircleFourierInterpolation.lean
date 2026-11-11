import ContinuousFlexibility.Analysis.OneHighCircleRealSobolev
import ContinuousFlexibility.Analysis.OneHighInterpolation

/-!
# The derivative trade used by tame circle composition

The common interpolation parameter trades one derivative between the input
function and the lift geometry. All endpoint memberships are supplied by the
actual smooth derivative towers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

theorem circle_sobolevNorm_trade_one_derivative
    (f g : ℕ → C(AddCircle P, ℂ))
    (hf : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (hg : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => g k (y : AddCircle P))
        (g (k + 1) (x : AddCircle P)) x) (r : ℕ) :
    circleSobolevNorm 4 (f 0) * circleSobolevNorm ((r + 2 : ℕ) : ℝ) (g 0) ≤
      circleSobolevNorm 3 (f 0) * circleSobolevNorm ((r + 3 : ℕ) : ℝ) (g 0) +
        circleSobolevNorm ((r + 4 : ℕ) : ℝ) (f 0) * circleSobolevNorm 2 (g 0) := by
  have hden : 0 < (r : ℝ) + 1 := by positivity
  apply frequencySobolevNorm_segment_product_le
    (measurable_of_countable _).aemeasurable
    (Eventually.of_forall (circleFrequencyWeight_pos P))
    (circle_frequencyWeighted_memLp_of_derivatives f hf 3)
    (circle_frequencyWeighted_memLp_of_derivatives f hf (r + 4))
    (circle_frequencyWeighted_memLp_of_derivatives g hg (r + 3))
    (circle_frequencyWeighted_memLp_of_derivatives g hg 2)
    (θ := (r : ℝ) / ((r : ℝ) + 1))
    ⟨div_nonneg (Nat.cast_nonneg r) hden.le, (div_le_one hden).mpr (by linarith)⟩
  · norm_num only [Nat.cast_add, Nat.cast_ofNat]
    field_simp [hden.ne'] <;> ring
  · norm_num only [Nat.cast_add, Nat.cast_ofNat]
    field_simp [hden.ne'] <;> ring

theorem circle_real_sobolevNorm_trade_one_derivative
    (f g : ℕ → C(AddCircle P, ℝ))
    (hf : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (hg : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => g k (y : AddCircle P))
        (g (k + 1) (x : AddCircle P)) x) (r : ℕ) :
    circleRealSobolevNorm 4 (f 0) * circleRealSobolevNorm ((r + 2 : ℕ) : ℝ) (g 0) ≤
      circleRealSobolevNorm 3 (f 0) * circleRealSobolevNorm ((r + 3 : ℕ) : ℝ) (g 0) +
        circleRealSobolevNorm ((r + 4 : ℕ) : ℝ) (f 0) * circleRealSobolevNorm 2 (g 0) :=
  circle_sobolevNorm_trade_one_derivative
    (fun k => circleComplexify (f k)) (fun k => circleComplexify (g k))
    (circleComplexify_hasDerivAt f hf) (circleComplexify_hasDerivAt g hg) r

end ContinuousFlexibility.Analysis
