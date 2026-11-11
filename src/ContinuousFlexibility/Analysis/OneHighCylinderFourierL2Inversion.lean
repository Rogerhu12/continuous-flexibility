import ContinuousFlexibility.Analysis.OneHighFrequencyNorms
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Pointwise inversion from an integrable actual `L²` Fourier transform

The physical function is only assumed continuous and square integrable.
Its actual `L²` Fourier transform is assumed integrable. Compatibility with
tempered distributions and the classical Fourier pairing identify the
continuous inverse integral with the original function. No physical `L¹`
or compact-support hypothesis is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory SchwartzMap Filter
open scoped ENNReal FourierTransform SchwartzMap

theorem real_continuous_fourierInv_of_integrable {g : ℝ → ℂ}
    (hg : Integrable g) : Continuous (𝓕⁻ g) := by
  have hm : MemLp g 1 := memLp_one_iff_integrable.mpr hg
  simpa only [Real.Lp.fourierTransformInv_toLp hm] using
    (Real.Lp.fourierTransformInv hm.toLp).continuous

/-- The ordinary inverse Fourier integral is self-adjoint under the
bilinear integral pairing of two integrable functions. -/
theorem real_integral_fourierInv_smul_eq {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, 𝓕⁻ f x • g x) = ∫ x : ℝ, f x • 𝓕⁻ g x := by
  simpa [Real.fourierInv_eq, VectorFourier.fourierIntegral, real_inner_comm] using
    VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := -(innerₗ ℝ)) Real.continuous_fourierChar continuous_inner.neg hf hg

/-- On the intersection `L¹ ∩ L²`, the classical inverse integral agrees
almost everywhere with the inverse of the actual `L²` Fourier isometry. -/
theorem real_l2_fourierInv_ae_eq_integral
    (g : Lp ℂ 2 (volume : Measure ℝ)) (hg : Integrable (g : ℝ → ℂ)) :
    ((𝓕⁻ g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      𝓕⁻ (g : ℝ → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ g)).locallyIntegrable (by norm_num))
    (real_continuous_fourierInv_of_integrable hg).locallyIntegrable
  intro a ha hcompact
  have hac : HasCompactSupport (Complex.ofRealCLM ∘ a) := hcompact.comp_left rfl
  have has : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ a) := by fun_prop
  let φ : 𝓢(ℝ, ℂ) := hac.toSchwartzMap has
  have hdist : (∫ x : ℝ, (𝓕⁻ φ) x • g x) =
      ∫ x : ℝ, φ x • (𝓕⁻ g : Lp ℂ 2 (volume : Measure ℝ)) x := by
    simpa only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] using
      congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ) (Lp.fourierInv_toTemperedDistribution_eq g)
  have hpair : (∫ x : ℝ, (𝓕⁻ φ) x • g x) =
      ∫ x : ℝ, φ x • 𝓕⁻ (g : ℝ → ℂ) x := by
    simpa only [SchwartzMap.fourierInv_coe] using
      real_integral_fourierInv_smul_eq φ.integrable hg
  calc
    (∫ x : ℝ, a x • (𝓕⁻ g : Lp ℂ 2 (volume : Measure ℝ)) x) =
        ∫ x : ℝ, φ x • (𝓕⁻ g : Lp ℂ 2 (volume : Measure ℝ)) x := by
      simp [φ, Complex.real_smul]
    _ = ∫ x : ℝ, (𝓕⁻ φ) x • g x := hdist.symm
    _ = ∫ x : ℝ, φ x • 𝓕⁻ (g : ℝ → ℂ) x := hpair
    _ = ∫ x : ℝ, a x • 𝓕⁻ (g : ℝ → ℂ) x := by
      simp [φ, Complex.real_smul]

/-- Pointwise inversion of a continuous `L²` function whose actual
`L²` Fourier transform is integrable. -/
theorem real_l2_fourierInv_eq_of_continuous (u : ℝ → ℂ) (hu : Continuous u)
    (hu2 : MemLp u 2 (volume : Measure ℝ))
    (hF1 : Integrable
      ((𝓕 (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) :
    𝓕⁻ (((𝓕 (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) = u := by
  have ha := real_l2_fourierInv_ae_eq_integral (𝓕 (hu2.toLp u)) hF1
  rw [FourierTransform.fourierInv_fourier_eq] at ha
  have he : u =ᵐ[volume]
      𝓕⁻ (((𝓕 (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) :=
    hu2.coeFn_toLp.symm.trans ha
  exact ((Continuous.ae_eq_iff_eq volume hu
    (real_continuous_fourierInv_of_integrable hF1)).mp he).symm

/-- The continuous representative is bounded pointwise by the `L¹` norm
of its actual `L²` Fourier transform. -/
theorem real_norm_le_fourierL1_of_continuous (u : ℝ → ℂ) (hu : Continuous u)
    (hu2 : MemLp u 2 (volume : Measure ℝ))
    (hF1 : Integrable
      ((𝓕 (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) (x : ℝ) :
    ‖u x‖ ≤ frequencyL1Norm volume
      (((𝓕 (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) := by
  let g : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hu2.toLp u)
  have hi : 𝓕⁻ (g : ℝ → ℂ) = u := real_l2_fourierInv_eq_of_continuous u hu hu2 hF1
  calc
    ‖u x‖ = ‖𝓕⁻ (g : ℝ → ℂ) x‖ := congrArg norm (congrFun hi x).symm
    _ ≤ ∫ ξ : ℝ, ‖g ξ‖ := by
      rw [Real.fourierInv_eq]
      exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Circle.norm_smul])
    _ = frequencyL1Norm volume (g : ℝ → ℂ) := by
      rw [frequencyL1Norm, toReal_eLpNorm,
        lpNorm_one_eq_integral_norm hF1.aestronglyMeasurable]

end ContinuousFlexibility.Analysis
