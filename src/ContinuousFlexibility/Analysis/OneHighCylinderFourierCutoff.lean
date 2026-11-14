module

public import ContinuousFlexibility.Analysis.OneHighCylinderDerivativeMultiplier
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Bounded physical-frequency cutoffs on the cylinder

Only the requested finite Sobolev membership is used for contraction.
Independently, bounded frequency support supplies every derivative moment
needed to construct genuine smooth inverse approximants.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

variable {P : ℝ}

def cylinderFrequencyCutoff (N : ℕ) (F : ℝ × ℤ → ℂ) (ζ : ℝ × ℤ) : ℂ :=
  if cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ) then F ζ else 0

theorem measurableSet_cylinderFrequencyCutoff (P : ℝ) (N : ℕ) :
    MeasurableSet {ζ : ℝ × ℤ |
      cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ)} :=
  (isClosed_le (continuous_cylinderFrequencyWeight _ _) continuous_const).measurableSet

theorem cylinderFrequencyCutoff_eq_indicator (N : ℕ) (F : ℝ × ℤ → ℂ) :
    cylinderFrequencyCutoff (P := P) N F =
      {ζ : ℝ × ℤ | cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ)}.indicator F := rfl

theorem measurable_cylinderFrequencyCutoff {F : ℝ × ℤ → ℂ} (hF : Measurable F) (N : ℕ) :
    Measurable (cylinderFrequencyCutoff (P := P) N F) := by
  rw [cylinderFrequencyCutoff_eq_indicator]
  exact hF.indicator (measurableSet_cylinderFrequencyCutoff P N)

theorem integrable_cylinderFrequencyCutoff {F : ℝ × ℤ → ℂ}
    (hF : Integrable F cylinderFrequencyMeasure) (N : ℕ) :
    Integrable (cylinderFrequencyCutoff (P := P) N F) cylinderFrequencyMeasure := by
  rw [cylinderFrequencyCutoff_eq_indicator]
  exact hF.indicator (measurableSet_cylinderFrequencyCutoff P N)

theorem cylinderFrequencyCutoff_memLp {F : ℝ × ℤ → ℂ} {p : ℝ≥0∞}
    (hF : MemLp F p cylinderFrequencyMeasure) (N : ℕ) :
    MemLp (cylinderFrequencyCutoff (P := P) N F) p cylinderFrequencyMeasure := by
  rw [cylinderFrequencyCutoff_eq_indicator]
  exact MemLp.indicator (measurableSet_cylinderFrequencyCutoff P N) hF

theorem cylinderFrequencyCutoff_eLpNorm_le (N : ℕ) (F : ℝ × ℤ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (cylinderFrequencyCutoff (P := P) N F) p cylinderFrequencyMeasure ≤
      eLpNorm F p cylinderFrequencyMeasure := by
  rw [cylinderFrequencyCutoff_eq_indicator]
  exact eLpNorm_indicator_le F (measurableSet_cylinderFrequencyCutoff P N)

theorem cylinderFrequencyCutoff_fourierL1_le {F : ℝ × ℤ → ℂ}
    (hF : MemLp F 1 cylinderFrequencyMeasure) (N : ℕ) :
    frequencyL1Norm cylinderFrequencyMeasure (cylinderFrequencyCutoff (P := P) N F) ≤
      frequencyL1Norm cylinderFrequencyMeasure F :=
  ENNReal.toReal_mono hF.ne (cylinderFrequencyCutoff_eLpNorm_le N F 1)

theorem cylinderFrequencyCutoff_weighted (N : ℕ) (F : ℝ × ℤ → ℂ) (s : ℝ) :
    frequencyWeighted (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s
      (cylinderFrequencyCutoff (P := P) N F) =
    cylinderFrequencyCutoff (P := P) N
      (frequencyWeighted (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s F) := by
  funext ζ
  by_cases h : cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ)
  · simp only [frequencyWeighted_apply, cylinderFrequencyCutoff, if_pos h]
  · simp only [frequencyWeighted_apply, cylinderFrequencyCutoff, if_neg h, smul_zero]

theorem cylinderFrequencyCutoff_weighted_memLp {F : ℝ × ℤ → ℂ} {s : ℝ}
    (hF : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s F)
        2 cylinderFrequencyMeasure) (N : ℕ) :
    MemLp (frequencyWeighted (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s
      (cylinderFrequencyCutoff (P := P) N F)) 2 cylinderFrequencyMeasure := by
  rw [cylinderFrequencyCutoff_weighted]
  exact cylinderFrequencyCutoff_memLp hF N

theorem cylinderFrequencyCutoff_sobolev_le {F : ℝ × ℤ → ℂ} {s : ℝ}
    (hF : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s F)
        2 cylinderFrequencyMeasure) (N : ℕ) :
    frequencySobolevNorm cylinderFrequencyMeasure
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s
        (cylinderFrequencyCutoff (P := P) N F) ≤
      frequencySobolevNorm cylinderFrequencyMeasure
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s F := by
  apply ENNReal.toReal_mono hF.ne
  rw [cylinderFrequencyCutoff_weighted]
  exact cylinderFrequencyCutoff_eLpNorm_le N _ 2

theorem cylinderFrequencyCutoff_mul_left (N : ℕ) (M F : ℝ × ℤ → ℂ) :
    (fun ζ => M ζ * cylinderFrequencyCutoff (P := P) N F ζ) =
      cylinderFrequencyCutoff (P := P) N (fun ζ => M ζ * F ζ) := by
  funext ζ
  by_cases h : cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ)
  · simp only [cylinderFrequencyCutoff, if_pos h]
  · simp only [cylinderFrequencyCutoff, if_neg h, mul_zero]

theorem norm_cylinderMultiplier_cutoff_le (N i j : ℕ) (F : ℝ × ℤ → ℂ) (ζ : ℝ × ℤ) :
    ‖cylinderDerivativeMultiplier P i j ζ * cylinderFrequencyCutoff (P := P) N F ζ‖ ≤
      (N : ℝ) ^ (i + j) * ‖F ζ‖ := by
  by_cases h : cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ)
  · rw [cylinderFrequencyCutoff, if_pos h, norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((norm_cylinderDerivativeMultiplier_le_weight P i j (i + j) le_rfl ζ).trans
        (pow_le_pow_left₀ (cylinderFrequencyWeight_pos _ _ ζ).le h _)) (norm_nonneg _)
  · rw [cylinderFrequencyCutoff, if_neg h, mul_zero, norm_zero]
    positivity

theorem integrable_cylinderMultiplier_cutoff {F : ℝ × ℤ → ℂ}
    (hF : Measurable F) (hF1 : Integrable F cylinderFrequencyMeasure) (N i j : ℕ) :
    Integrable (fun ζ => cylinderDerivativeMultiplier P i j ζ *
      cylinderFrequencyCutoff (P := P) N F ζ) cylinderFrequencyMeasure := by
  apply (hF1.norm.const_mul ((N : ℝ) ^ (i + j))).mono'
    ((measurable_cylinderDerivativeMultiplier P i j).mul
      (measurable_cylinderFrequencyCutoff hF N)).aestronglyMeasurable
  exact Eventually.of_forall (norm_cylinderMultiplier_cutoff_le N i j F)

theorem cylinderMultiplier_cutoff_memLp_two {F : ℝ × ℤ → ℂ}
    (hF : Measurable F) (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N i j : ℕ) :
    MemLp (fun ζ => cylinderDerivativeMultiplier P i j ζ *
      cylinderFrequencyCutoff (P := P) N F ζ) 2 cylinderFrequencyMeasure := by
  apply (hF2.const_smul ((N : ℝ) ^ (i + j))).of_le
    ((measurable_cylinderDerivativeMultiplier P i j).mul
      (measurable_cylinderFrequencyCutoff hF N)).aestronglyMeasurable
  exact Eventually.of_forall fun ζ => by
    simpa only [Pi.mul_apply, Pi.smul_apply, norm_smul, Real.norm_of_nonneg
      (pow_nonneg (Nat.cast_nonneg N) (i + j))] using norm_cylinderMultiplier_cutoff_le N i j F ζ

/-- Every natural Sobolev weight is bounded on the cutoff support. -/
theorem cylinderFrequencyCutoff_weighted_memLp_all {F : ℝ × ℤ → ℂ}
    (hF : Measurable F) (hF2 : MemLp F 2 cylinderFrequencyMeasure) (N s : ℕ) :
    MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFrequencyCutoff (P := P) N F)) 2 cylinderFrequencyMeasure := by
  apply (hF2.const_smul ((N : ℝ) ^ s)).of_le
    (frequencyWeighted_aestronglyMeasurable
      (continuous_cylinderFrequencyWeight _ _).measurable.aemeasurable
      (measurable_cylinderFrequencyCutoff hF N).aestronglyMeasurable _)
  exact Eventually.of_forall fun ζ => by
    simp only [Pi.smul_apply, norm_smul,
      Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg N) s)]
    rw [cylinder_norm_frequencyWeighted_nat]
    by_cases h : cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ)
    · rw [cylinderFrequencyCutoff, if_pos h]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (cylinderFrequencyWeight_pos _ _ ζ).le h s) (norm_nonneg _)
    · rw [cylinderFrequencyCutoff, if_neg h, norm_zero, mul_zero]
      positivity

end ContinuousFlexibility.Analysis
