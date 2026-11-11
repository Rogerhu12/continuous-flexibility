import ContinuousFlexibility.Analysis.OneHighCircleFourierProduct
import ContinuousFlexibility.Analysis.OneHighCircleFourierWeightArithmetic
import ContinuousFlexibility.Analysis.OneHighCircleSobolevJetsBasic
import ContinuousFlexibility.Analysis.OneHighConvolutionYoung

/-!
# The whole Sobolev product estimate on a circle

The output Bessel weight in the actual convolution is placed on one input
factor at a time. Young's inequality then gives the two-factor Sobolev estimate
directly, with the explicit constant `2 ^ s` and without a finite Fourier
support hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal NNReal MeasureTheory

variable {P : ℝ} [Fact (0 < P)]

/-- The physical output weight can be distributed to the two inputs in
the complete Fourier convolution of an actual product. -/
theorem circle_enorm_weighted_fourierCoeff_mul_le (s : ℕ)
    (f g : C(AddCircle P, ℂ)) (hf : MemLp (fourierCoeff f) 1 Measure.count) (n : ℤ) :
    ‖frequencyWeighted (circleFrequencyWeight P) (s : ℝ) (fourierCoeff (f * g)) n‖ₑ ≤
      (2 : ℝ≥0∞) ^ s *
        (((fun k : ℤ => ENNReal.ofReal (circleFrequencyWeight P k) ^ s *
            ‖fourierCoeff f k‖ₑ) ⋆ₗ[Measure.count]
            (fun k : ℤ => ‖fourierCoeff g k‖ₑ)) n +
          ((fun k : ℤ => ‖fourierCoeff f k‖ₑ) ⋆ₗ[Measure.count]
            (fun k : ℤ => ENNReal.ofReal (circleFrequencyWeight P k) ^ s *
              ‖fourierCoeff g k‖ₑ)) n) := by
  rw [circle_enorm_frequencyWeighted_nat]
  apply (mul_le_mul_left'
    (circle_enorm_fourierCoeff_mul_le_lconvolution f g hf n)
    (ENNReal.ofReal (circleFrequencyWeight P n) ^ s)).trans
  rw [lconvolution_def, lconvolution_def, lconvolution_def]
  simp only [lintegral_count]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  have hw := circleFrequencyWeight_add_pow_ennreal_le P k (-k + n) s
  rw [show k + (-k + n) = n by omega] at hw
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ s *
        (ENNReal.ofReal (circleFrequencyWeight P k) ^ s +
          ENNReal.ofReal (circleFrequencyWeight P (-k + n)) ^ s)) *
        (‖fourierCoeff f k‖ₑ * ‖fourierCoeff g (-k + n)‖ₑ) :=
      mul_le_mul_right' hw _
    _ = _ := by ring

/-- The weighted Fourier `L²` estimate before converting finite norms to
real numbers. The identity of the actual product is retained throughout. -/
theorem circle_eLpNorm_weighted_fourierCoeff_mul_le (s : ℕ)
    (f g : C(AddCircle P, ℂ)) (hf : MemLp (fourierCoeff f) 1 Measure.count) :
    eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
        (fourierCoeff (f * g))) 2 Measure.count ≤
      (2 : ℝ≥0∞) ^ s *
        (eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
            (fourierCoeff f)) 2 Measure.count * eLpNorm (fourierCoeff g) 1 Measure.count +
          eLpNorm (fourierCoeff f) 1 Measure.count *
            eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
              (fourierCoeff g)) 2 Measure.count) := by
  let A : ℤ → ℝ≥0∞ :=
    (fun k : ℤ => ENNReal.ofReal (circleFrequencyWeight P k) ^ s * ‖fourierCoeff f k‖ₑ)
      ⋆ₗ[Measure.count] (fun k : ℤ => ‖fourierCoeff g k‖ₑ)
  let B : ℤ → ℝ≥0∞ :=
    (fun k : ℤ => ‖fourierCoeff f k‖ₑ) ⋆ₗ[Measure.count]
      (fun k : ℤ => ENNReal.ofReal (circleFrequencyWeight P k) ^ s * ‖fourierCoeff g k‖ₑ)
  have hscale : (((2 : ℝ≥0) ^ s : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ s := by simp
  have hscaled :
      eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
          (fourierCoeff (f * g))) 2 Measure.count ≤
        (2 : ℝ≥0∞) ^ s * eLpNorm (A + B) 2 Measure.count := by
    have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
      (μ := Measure.count) (c := (2 : ℝ≥0) ^ s) (g := A + B)
      (f := frequencyWeighted (circleFrequencyWeight P) (s : ℝ) (fourierCoeff (f * g)))
      (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall (fun n => by
        simpa only [hscale, Pi.add_apply, enorm_eq_self, A, B] using
          circle_enorm_weighted_fourierCoeff_mul_le s f g hf n)) 2
    simpa only [ENNReal.smul_def, hscale] using h
  have hnorm (v : C(AddCircle P, ℂ)) :
      eLpNorm (fun n : ℤ => ‖fourierCoeff v n‖ₑ) 1 Measure.count =
        eLpNorm (fourierCoeff v) 1 Measure.count :=
    eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable
  have hA : eLpNorm A 2 Measure.count ≤
      eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
        (fourierCoeff f)) 2 Measure.count * eLpNorm (fourierCoeff g) 1 Measure.count := by
    have h := lconvolution_eLpNorm_two_le' (μ := Measure.count)
      (f := fun k : ℤ => ENNReal.ofReal (circleFrequencyWeight P k) ^ s *
        ‖fourierCoeff f k‖ₑ) (g := fun k : ℤ => ‖fourierCoeff g k‖ₑ)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
    simpa only [A, circle_eLpNorm_weighted_enorm, hnorm g] using h
  have hB : eLpNorm B 2 Measure.count ≤
      eLpNorm (fourierCoeff f) 1 Measure.count *
        eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
          (fourierCoeff g)) 2 Measure.count := by
    have h := lconvolution_eLpNorm_two_le (μ := Measure.count)
      (f := fun k : ℤ => ‖fourierCoeff f k‖ₑ)
      (g := fun k : ℤ => ENNReal.ofReal (circleFrequencyWeight P k) ^ s *
        ‖fourierCoeff g k‖ₑ)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
    simpa only [B, circle_eLpNorm_weighted_enorm, hnorm f] using h
  exact hscaled.trans (mul_le_mul_left'
    ((eLpNorm_add_le (f := A) (g := B) (p := (2 : ℝ≥0∞)) (μ := Measure.count)
      (by norm_num)).trans (add_le_add hA hB)) _)

/-- The product has finite physical Sobolev norm whenever both factors
have finite Sobolev and absolute Fourier norms. -/
theorem circle_frequencyWeighted_mul_memLp (s : ℕ) (f g : C(AddCircle P, ℂ))
    (hf : MemLp (fourierCoeff f) 1 Measure.count)
    (hg : MemLp (fourierCoeff g) 1 Measure.count)
    (hfs : MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff f)) 2 Measure.count)
    (hgs : MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff g)) 2 Measure.count) :
    MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff (f * g))) 2 Measure.count := by
  apply memLp_iff.mpr
  apply (circle_eLpNorm_weighted_fourierCoeff_mul_le s f g hf).trans_lt
  exact ENNReal.mul_lt_top (by simp)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hfs hg, ENNReal.mul_lt_top hf hgs⟩)

/-- The whole circle `H^s` two-factor product estimate with exactly one
high norm in each term. It includes `s = 0`. -/
theorem circle_frequencySobolevNorm_mul_le (s : ℕ) (f g : C(AddCircle P, ℂ))
    (hf : MemLp (fourierCoeff f) 1 Measure.count)
    (hg : MemLp (fourierCoeff g) 1 Measure.count)
    (hfs : MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff f)) 2 Measure.count)
    (hgs : MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff g)) 2 Measure.count) :
    frequencySobolevNorm Measure.count (circleFrequencyWeight P) (s : ℝ)
        (fourierCoeff (f * g)) ≤
      (2 : ℝ) ^ s *
        (frequencySobolevNorm Measure.count (circleFrequencyWeight P) (s : ℝ)
            (fourierCoeff f) * frequencyL1Norm Measure.count (fourierCoeff g) +
          frequencyL1Norm Measure.count (fourierCoeff f) *
            frequencySobolevNorm Measure.count (circleFrequencyWeight P) (s : ℝ)
              (fourierCoeff g)) := by
  have hfg := ENNReal.mul_ne_top hfs.ne hg.ne
  have hgf := ENNReal.mul_ne_top hf.ne hgs.ne
  have hfinite := ENNReal.mul_ne_top (by simp : (2 : ℝ≥0∞) ^ s ≠ ∞)
    (ENNReal.add_ne_top.mpr ⟨hfg, hgf⟩)
  have h := ENNReal.toReal_mono hfinite
    (circle_eLpNorm_weighted_fourierCoeff_mul_le s f g hf)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_add hfg hgf,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, frequencySobolevNorm, frequencyL1Norm] using h

end ContinuousFlexibility.Analysis
