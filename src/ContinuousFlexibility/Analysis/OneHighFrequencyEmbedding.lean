import ContinuousFlexibility.Analysis.OneHighFrequencyNorms

/-!
# The inverse-weight Fourier embedding estimate

Cauchy--Schwarz turns a square-integrable inverse weight and weighted frequency
data into integrable Fourier data, with the exact product of the two `L²` norms.
Circle and cylinder embeddings differ only in their inverse-weight integral.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem inverse_weight_cancel {μ : Measure Ω} {W : Ω → ℝ} {f : Ω → ℂ}
    (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ) (s : ℝ) :
    (fun ξ => (W ξ ^ (-s) : ℝ) • frequencyWeighted W s f ξ) =ᵐ[μ] f := by
  filter_upwards [hWpos] with ξ hξ
  rw [frequencyWeighted_apply, smul_smul, ← Real.rpow_add hξ,
    neg_add_cancel, Real.rpow_zero, one_smul]

/-- The two `L²` memberships give actual `L¹` membership of the Fourier data. -/
theorem frequency_memLp_one_of_inverse_weight {μ : Measure Ω} {W : Ω → ℝ}
    {f : Ω → ℂ} {s : ℝ} (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ)
    (hInv : MemLp (fun ξ => W ξ ^ (-s)) 2 μ)
    (hs : MemLp (frequencyWeighted W s f) 2 μ) : MemLp f 1 μ := by
  exact (memLp_congr_ae (inverse_weight_cancel hWpos s)).mp (hInv.smul hs)

/-- Cauchy--Schwarz for a positive frequency weight, before taking `toReal`. -/
theorem frequency_eLpNorm_one_le_inverse_weight_mul {μ : Measure Ω} {W : Ω → ℝ}
    {f : Ω → ℂ} {s : ℝ} (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ)
    (hInv : MemLp (fun ξ => W ξ ^ (-s)) 2 μ)
    (hs : MemLp (frequencyWeighted W s f) 2 μ) :
    eLpNorm f 1 μ ≤ eLpNorm (fun ξ => W ξ ^ (-s)) 2 μ *
      eLpNorm (frequencyWeighted W s f) 2 μ := by
  rw [← eLpNorm_congr_ae (inverse_weight_cancel hWpos s)]
  exact eLpNorm_smul_le_mul_eLpNorm hInv.aestronglyMeasurable hs.aestronglyMeasurable

/-- The Fourier `L¹` norm is controlled by the weighted Sobolev norm and the
`L²` norm of the inverse weight. No integrability premise on the unweighted
frequency data is required. -/
theorem frequencyL1Norm_le_inverse_weight_mul {μ : Measure Ω} {W : Ω → ℝ}
    {f : Ω → ℂ} {s : ℝ} (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ)
    (hInv : MemLp (fun ξ => W ξ ^ (-s)) 2 μ)
    (hs : MemLp (frequencyWeighted W s f) 2 μ) :
    frequencyL1Norm μ f ≤ (eLpNorm (fun ξ => W ξ ^ (-s)) 2 μ).toReal *
      frequencySobolevNorm μ W s f := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hInv.ne hs.ne)
    (frequency_eLpNorm_one_le_inverse_weight_mul hWpos hInv hs)
  simpa only [frequencyL1Norm, frequencySobolevNorm, ENNReal.toReal_mul] using h

end ContinuousFlexibility.Analysis
