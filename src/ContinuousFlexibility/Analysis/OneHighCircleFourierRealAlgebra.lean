module

public import ContinuousFlexibility.Analysis.OneHighCircleRealSobolev
public import ContinuousFlexibility.Analysis.OneHighCircleSobolevAlgebra
public import ContinuousFlexibility.Analysis.OneHighCircleFourierSobolevProduct

/-!
# Real-function algebra for the physical circle norms

These are the canonical complexification forms of the verified Fourier
estimates, used by the real circle diffeomorphism and flow arguments.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

@[simp] theorem circleComplexify_add (f g : C(AddCircle P, ℝ)) :
    circleComplexify (f + g) = circleComplexify f + circleComplexify g := by
  ext θ
  simp only [circleComplexify_apply, ContinuousMap.add_apply, Complex.ofReal_add]

@[simp] theorem circleComplexify_mul (f g : C(AddCircle P, ℝ)) :
    circleComplexify (f * g) = circleComplexify f * circleComplexify g := by
  ext θ
  simp only [circleComplexify_apply, ContinuousMap.mul_apply, Complex.ofReal_mul]

@[simp] theorem circleComplexify_one :
    circleComplexify (1 : C(AddCircle P, ℝ)) = (1 : C(AddCircle P, ℂ)) := by
  ext θ
  simp only [circleComplexify_apply, ContinuousMap.one_apply, Complex.ofReal_one]

theorem circle_real_sobolevNorm_nonneg (s : ℝ) (f : C(AddCircle P, ℝ)) :
    0 ≤ circleRealSobolevNorm s f := circle_sobolevNorm_nonneg s (circleComplexify f)

theorem circle_real_sobolevNorm_mono_of_derivatives (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x) {a b : ℕ} (hab : a ≤ b) :
    circleRealSobolevNorm (a : ℝ) (f 0) ≤ circleRealSobolevNorm (b : ℝ) (f 0) :=
  circle_sobolevNorm_mono_of_derivatives (fun k => circleComplexify (f k))
    (circleComplexify_hasDerivAt f hderiv) hab

theorem circle_real_sobolevNorm_derivative_le (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x) (s k : ℕ) :
    circleRealSobolevNorm (s : ℝ) (f k) ≤
      circleRealSobolevNorm ((s + k : ℕ) : ℝ) (f 0) :=
  circle_sobolevNorm_derivative_le (fun k => circleComplexify (f k))
    (circleComplexify_hasDerivAt f hderiv) s k

theorem circle_real_sobolevNorm_succ_le_l2_add_derivative
    (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x) (s : ℕ) :
    circleRealSobolevNorm ((s + 1 : ℕ) : ℝ) (f 0) ≤ (2 : ℝ) ^ (s + 1) *
      ((eLpNorm (f 0) 2 AddCircle.haarAddCircle).toReal +
        circleRealSobolevNorm (s : ℝ) (f 1)) := by
  simpa only [circle_eLpNorm_complexify] using
    circle_sobolevNorm_succ_le_l2_add_derivative (fun k => circleComplexify (f k))
      (circleComplexify_hasDerivAt f hderiv) s

theorem circle_real_sobolevNorm_add_le (f g : C(AddCircle P, ℝ)) (s : ℝ)
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) s
      (fourierCoeff (circleComplexify f))) 2 Measure.count)
    (hg : MemLp (frequencyWeighted (circleFrequencyWeight P) s
      (fourierCoeff (circleComplexify g))) 2 Measure.count) :
    circleRealSobolevNorm s (f + g) ≤ circleRealSobolevNorm s f + circleRealSobolevNorm s g := by
  simpa only [circleRealSobolevNorm, circleComplexify_add] using
    circle_sobolevNorm_add_le (circleComplexify f) (circleComplexify g) s hf hg

@[simp] theorem circle_real_sobolevNorm_one (s : ℝ) :
    circleRealSobolevNorm s (1 : C(AddCircle P, ℝ)) = 1 := by
  rw [circleRealSobolevNorm, circleComplexify_one]
  exact circle_sobolevNorm_one s

theorem circle_real_norm_apply_le_sobolev_one_of_derivatives
    (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x) (k : ℕ) (θ : AddCircle P) :
    ‖f k θ‖ ≤ circleSobolevEmbeddingConstant P * circleRealSobolevNorm 1 (f k) := by
  have h := ((circleComplexify (f k)).norm_coe_le_norm θ).trans
    (circle_supNorm_le_sobolev_one_of_derivatives (fun j => circleComplexify (f j))
      (circleComplexify_hasDerivAt f hderiv) k)
  simpa only [circleComplexify_apply, Complex.norm_real] using h

theorem circle_real_fourierL1Norm_le_sobolev_one_of_derivatives
    (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x) (k : ℕ) :
    circleRealFourierL1Norm (f k) ≤
      circleSobolevEmbeddingConstant P * circleRealSobolevNorm 1 (f k) := by
  apply circle_fourierL1Norm_le_sobolev_one
  simpa only [Nat.cast_one] using circle_frequencyWeighted_memLp_of_derivatives_at
    (fun j => circleComplexify (f j)) (circleComplexify_hasDerivAt f hderiv) 1 k

theorem circle_real_sobolevNorm_mul_le_of_derivatives
    (f g : ℕ → C(AddCircle P, ℝ))
    (hf : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (hg : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => g k (y : AddCircle P))
        (g (k + 1) (x : AddCircle P)) x) (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (f 0 * g 0) ≤ (2 : ℝ) ^ s *
      (circleRealSobolevNorm (s : ℝ) (f 0) * circleRealFourierL1Norm (g 0) +
        circleRealFourierL1Norm (f 0) * circleRealSobolevNorm (s : ℝ) (g 0)) := by
  have h := circle_frequencySobolevNorm_mul_le s (circleComplexify (f 0))
    (circleComplexify (g 0))
    (circle_fourier_memLp_one_of_derivatives (fun k => circleComplexify (f k))
      (circleComplexify_hasDerivAt f hf) 0)
    (circle_fourier_memLp_one_of_derivatives (fun k => circleComplexify (g k))
      (circleComplexify_hasDerivAt g hg) 0)
    (circle_frequencyWeighted_memLp_of_derivatives (fun k => circleComplexify (f k))
      (circleComplexify_hasDerivAt f hf) s)
    (circle_frequencyWeighted_memLp_of_derivatives (fun k => circleComplexify (g k))
      (circleComplexify_hasDerivAt g hg) s)
  simpa only [circleRealSobolevNorm, circleComplexify_mul] using h

end ContinuousFlexibility.Analysis
