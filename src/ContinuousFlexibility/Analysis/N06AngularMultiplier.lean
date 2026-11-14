module

public import ContinuousFlexibility.Analysis.OneHighCircleSobolevAlgebra
public import ContinuousFlexibility.Analysis.OneHighCircleFourierSobolevProduct

/-!
# Multiplication on the fixed angular source order

The one-high Fourier convolution inequality and the existing circle Sobolev
embedding imply bounded multiplication at every integer order at least one.
No derivative of the source beyond that same order is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

/-- Finiteness of a larger natural Sobolev order implies finiteness of
every smaller order, on the same actual Fourier coefficients. -/
theorem n06_circle_frequencyWeighted_memLp_mono (f : AddCircle P → ℂ)
    {a b : ℕ} (hab : a ≤ b)
    (hb : MemLp (frequencyWeighted (circleFrequencyWeight P) (b : ℝ)
      (fourierCoeff f)) 2 Measure.count) :
    MemLp (frequencyWeighted (circleFrequencyWeight P) (a : ℝ)
      (fourierCoeff f)) 2 Measure.count := by
  apply hb.mono (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall fun n => by
    rw [circle_norm_frequencyWeighted_nat, circle_norm_frequencyWeighted_nat]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (circleFrequencyWeight_one_le P n) hab) (norm_nonneg _)

/-- The coefficient multiplication operator is bounded on precisely the
fixed source Sobolev order. This is a direct consequence of the actual
Fourier product theorem, with the two Fourier L¹ norms supplied by H¹. -/
theorem n06_circle_sobolev_mul_bound (b : ℕ) (hb : 1 ≤ b)
    (f g : C(AddCircle P, ℂ))
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) (b : ℝ)
      (fourierCoeff f)) 2 Measure.count)
    (hg : MemLp (frequencyWeighted (circleFrequencyWeight P) (b : ℝ)
      (fourierCoeff g)) 2 Measure.count) :
    MemLp (frequencyWeighted (circleFrequencyWeight P) (b : ℝ)
      (fourierCoeff (f * g))) 2 Measure.count ∧
    circleSobolevNorm (b : ℝ) (f * g) ≤
      (2 : ℝ) ^ (b + 1) * circleSobolevEmbeddingConstant P *
        circleSobolevNorm (b : ℝ) f * circleSobolevNorm (b : ℝ) g := by
  have hf1 : MemLp (frequencyWeighted (circleFrequencyWeight P) 1
      (fourierCoeff f)) 2 Measure.count := by
    simpa only [Nat.cast_one] using
      n06_circle_frequencyWeighted_memLp_mono f hb hf
  have hg1 : MemLp (frequencyWeighted (circleFrequencyWeight P) 1
      (fourierCoeff g)) 2 Measure.count := by
    simpa only [Nat.cast_one] using
      n06_circle_frequencyWeighted_memLp_mono g hb hg
  have hfL := circle_fourier_memLp_one_of_h1 hf1
  have hgL := circle_fourier_memLp_one_of_h1 hg1
  have hC : 0 ≤ circleSobolevEmbeddingConstant P :=
    zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  have hfm : circleSobolevNorm 1 f ≤ circleSobolevNorm (b : ℝ) f := by
    simpa only [Nat.cast_one] using circle_sobolevNorm_mono f hb hf
  have hgm : circleSobolevNorm 1 g ≤ circleSobolevNorm (b : ℝ) g := by
    simpa only [Nat.cast_one] using circle_sobolevNorm_mono g hb hg
  have hfl : frequencyL1Norm Measure.count (fourierCoeff f) ≤
      circleSobolevEmbeddingConstant P * circleSobolevNorm (b : ℝ) f :=
    (circle_fourierL1Norm_le_sobolev_one hf1).trans
      (mul_le_mul_of_nonneg_left hfm hC)
  have hgl : frequencyL1Norm Measure.count (fourierCoeff g) ≤
      circleSobolevEmbeddingConstant P * circleSobolevNorm (b : ℝ) g :=
    (circle_fourierL1Norm_le_sobolev_one hg1).trans
      (mul_le_mul_of_nonneg_left hgm hC)
  refine ⟨circle_frequencyWeighted_mul_memLp b f g hfL hgL hf hg, ?_⟩
  have hproduct := circle_frequencySobolevNorm_mul_le b f g hfL hgL hf hg
  change circleSobolevNorm (b : ℝ) (f * g) ≤
    (2 : ℝ) ^ b * (circleSobolevNorm (b : ℝ) f *
      frequencyL1Norm Measure.count (fourierCoeff g) +
      frequencyL1Norm Measure.count (fourierCoeff f) *
        circleSobolevNorm (b : ℝ) g) at hproduct
  calc
    circleSobolevNorm (b : ℝ) (f * g) ≤
        (2 : ℝ) ^ b * (circleSobolevNorm (b : ℝ) f *
          frequencyL1Norm Measure.count (fourierCoeff g) +
          frequencyL1Norm Measure.count (fourierCoeff f) *
            circleSobolevNorm (b : ℝ) g) := hproduct
    _ ≤ (2 : ℝ) ^ b * (circleSobolevNorm (b : ℝ) f *
          (circleSobolevEmbeddingConstant P * circleSobolevNorm (b : ℝ) g) +
          (circleSobolevEmbeddingConstant P * circleSobolevNorm (b : ℝ) f) *
            circleSobolevNorm (b : ℝ) g) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left hgl (circle_sobolevNorm_nonneg _ _))
          (mul_le_mul_of_nonneg_right hfl (circle_sobolevNorm_nonneg _ _)))
        (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- A uniformly small coefficient gives a uniformly small multiplier on
the same source order; the source loses no angular derivatives. -/
theorem n06_circle_small_multiplier (b : ℕ) (hb : 1 ≤ b)
    (f g : C(AddCircle P, ℂ)) {δ : ℝ}
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) (b : ℝ)
      (fourierCoeff f)) 2 Measure.count)
    (hg : MemLp (frequencyWeighted (circleFrequencyWeight P) (b : ℝ)
      (fourierCoeff g)) 2 Measure.count)
    (hδ : circleSobolevNorm (b : ℝ) f ≤ δ) :
    circleSobolevNorm (b : ℝ) (f * g) ≤
      ((2 : ℝ) ^ (b + 1) * circleSobolevEmbeddingConstant P * δ) *
        circleSobolevNorm (b : ℝ) g := by
  have hC : 0 ≤ (2 : ℝ) ^ (b + 1) * circleSobolevEmbeddingConstant P :=
    mul_nonneg (by positivity)
      (zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P))
  exact (n06_circle_sobolev_mul_bound b hb f g hf hg).2.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ hC)
      (circle_sobolevNorm_nonneg _ _))

end ContinuousFlexibility.Analysis
