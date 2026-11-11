import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Frequency weights and Sobolev norms

The weight and frequency measure are explicit. This allows the same estimates
to apply to counting measure on circle frequencies and to the product of
Lebesgue and counting measures on cylinder frequencies. Finiteness is expressed
by actual `MemLp` hypotheses; taking `toReal` alone does not assert finiteness.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Multiplication of frequency data by a real power of a positive weight. -/
def frequencyWeighted (W : Ω → ℝ) (s : ℝ) (f : Ω → ℂ) : Ω → ℂ :=
  fun ξ => (W ξ ^ s : ℝ) • f ξ

/-- The real-valued weighted Fourier `L²` norm. Its finiteness must be supplied
as a `MemLp (frequencyWeighted W s f) 2 μ` hypothesis. -/
def frequencySobolevNorm (μ : Measure Ω) (W : Ω → ℝ) (s : ℝ)
    (f : Ω → ℂ) : ℝ :=
  (eLpNorm (frequencyWeighted W s f) 2 μ).toReal

/-- The real-valued Fourier `L¹` norm. -/
def frequencyL1Norm (μ : Measure Ω) (f : Ω → ℂ) : ℝ :=
  (eLpNorm f 1 μ).toReal

@[simp]
theorem frequencyWeighted_apply (W : Ω → ℝ) (s : ℝ) (f : Ω → ℂ) (ξ : Ω) :
    frequencyWeighted W s f ξ = (W ξ ^ s : ℝ) • f ξ := rfl

@[simp]
theorem frequencyWeighted_zero (W : Ω → ℝ) (f : Ω → ℂ) :
    frequencyWeighted W 0 f = f := by
  ext ξ
  simp only [frequencyWeighted_apply, Real.rpow_zero, one_smul]

theorem frequencySobolevNorm_nonneg (μ : Measure Ω) (W : Ω → ℝ) (s : ℝ)
    (f : Ω → ℂ) : 0 ≤ frequencySobolevNorm μ W s f :=
  ENNReal.toReal_nonneg

theorem frequencyL1Norm_nonneg (μ : Measure Ω) (f : Ω → ℂ) :
    0 ≤ frequencyL1Norm μ f :=
  ENNReal.toReal_nonneg

theorem frequencyWeighted_aestronglyMeasurable {μ : Measure Ω} {W : Ω → ℝ}
    {f : Ω → ℂ} (hW : AEMeasurable W μ) (hf : AEStronglyMeasurable f μ) (s : ℝ) :
    AEStronglyMeasurable (frequencyWeighted W s f) μ :=
  (hW.pow_const s).aestronglyMeasurable.fun_smul hf

/-- A positive weight cannot hide a failure of measurability of the frequency data. -/
theorem frequencyWeighted_aestronglyMeasurable_iff {μ : Measure Ω} {W : Ω → ℝ}
    {f : Ω → ℂ} (hW : AEMeasurable W μ) (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ) (s : ℝ) :
    AEStronglyMeasurable (frequencyWeighted W s f) μ ↔ AEStronglyMeasurable f μ := by
  apply aestronglyMeasurable_smul_iff₀ (hW.pow_const s).aestronglyMeasurable
  filter_upwards [hWpos] with ξ hξ
  exact (Real.rpow_pos_of_pos hξ s).ne'

theorem frequencyWeighted_enorm {W : Ω → ℝ} {s : ℝ} {f : Ω → ℂ} {ξ : Ω}
    (hξ : 0 < W ξ) :
    ‖frequencyWeighted W s f ξ‖ₑ = ENNReal.ofReal (W ξ) ^ s * ‖f ξ‖ₑ := by
  rw [frequencyWeighted_apply, enorm_smul,
    Real.enorm_of_nonneg (Real.rpow_nonneg hξ.le s),
    ← ENNReal.ofReal_rpow_of_pos hξ]

/-- The pointwise multiplicative identity underlying interpolation. It remains
valid when the frequency datum vanishes and at either endpoint of the segment. -/
theorem frequencyWeighted_enorm_interpolate {W : Ω → ℝ} {f : Ω → ℂ} {ξ : Ω}
    (hξ : 0 < W ξ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (k m : ℝ) :
    ‖frequencyWeighted W (θ * k + (1 - θ) * m) f ξ‖ₑ =
      ‖frequencyWeighted W k f ξ‖ₑ ^ θ *
        ‖frequencyWeighted W m f ξ‖ₑ ^ (1 - θ) := by
  rw [frequencyWeighted_enorm hξ, frequencyWeighted_enorm hξ,
    frequencyWeighted_enorm hξ]
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
  have hW0 : ENNReal.ofReal (W ξ) ≠ 0 := (ENNReal.ofReal_pos.mpr hξ).ne'
  have hsum : θ + (1 - θ) = 1 := by ring
  have hexp : k * θ + m * (1 - θ) = θ * k + (1 - θ) * m := by ring
  symm
  calc
    (ENNReal.ofReal (W ξ) ^ k * ‖f ξ‖ₑ) ^ θ *
        (ENNReal.ofReal (W ξ) ^ m * ‖f ξ‖ₑ) ^ (1 - θ) =
        (ENNReal.ofReal (W ξ) ^ (k * θ) *
          ENNReal.ofReal (W ξ) ^ (m * (1 - θ))) *
          (‖f ξ‖ₑ ^ θ * ‖f ξ‖ₑ ^ (1 - θ)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.1,
        ENNReal.mul_rpow_of_nonneg _ _ hθ',
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      ac_rfl
    _ = ENNReal.ofReal (W ξ) ^ (k * θ + m * (1 - θ)) *
        ‖f ξ‖ₑ ^ (θ + (1 - θ)) := by
      rw [← ENNReal.rpow_add _ _ hW0 ENNReal.ofReal_ne_top,
        ← ENNReal.rpow_add_of_nonneg _ _ hθ.1 hθ']
    _ = ENNReal.ofReal (W ξ) ^ (θ * k + (1 - θ) * m) * ‖f ξ‖ₑ := by
      rw [hexp, hsum, ENNReal.rpow_one]

end ContinuousFlexibility.Analysis
