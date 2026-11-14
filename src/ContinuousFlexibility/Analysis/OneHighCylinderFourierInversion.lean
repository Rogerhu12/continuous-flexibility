module

public import ContinuousFlexibility.Analysis.OneHighCylinderPlancherel
public import ContinuousFlexibility.Analysis.OneHighCylinderFourierL2Inversion
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Pointwise inversion and the Fourier `L¹` bound on the cylinder

Fubini gives integrability of every integer Fourier mode. The actual radial
`L²` inverse recovers the angular coefficients pointwise. Their absolute
sum is bounded by the mixed Fourier `L¹` norm, so ordinary circle inversion
recovers the original continuous cylinder function.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal FourierTransform

variable {P : ℝ} [Fact (0 < P)]

theorem cylinderFourierMode_integrable (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hL2) 1 cylinderFrequencyMeasure) (n : ℤ) :
    Integrable (cylinderFourierMode f hf hL2 n : ℝ → ℂ) := by
  have hi : Integrable (cylinderFourier f hf hL2) (volume.prod Measure.count) :=
    memLp_one_iff_integrable.mp hF1
  exact (Measure.ae_count_iff.mp hi.prod_left_ae) n

/-- The inverse radial transform recovers the actual angular coefficient
at every radial point, without radial `L¹` assumptions on that coefficient. -/
theorem cylinderAngularCoefficient_fourierInv
    (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hL2) 1 cylinderFrequencyMeasure) (n : ℤ) :
    𝓕⁻ (cylinderFourierMode f hf hL2 n : ℝ → ℂ) = cylinderAngularCoefficient f n :=
  real_l2_fourierInv_eq_of_continuous (cylinderAngularCoefficient f n)
    (continuous_cylinderAngularCoefficient hf n) (cylinderAngularCoefficient_memLp hf hL2 n)
    (cylinderFourierMode_integrable f hf hL2 hF1 n)

theorem cylinderAngularCoefficient_norm_le_frequency_integral
    (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hL2) 1 cylinderFrequencyMeasure) (n : ℤ) (r : ℝ) :
    ‖cylinderAngularCoefficient f n r‖ ≤
      ∫ ξ : ℝ, ‖cylinderFourier f hf hL2 (ξ, n)‖ := by
  have hmode := cylinderFourierMode_integrable f hf hL2 hF1 n
  have hb := real_norm_le_fourierL1_of_continuous (cylinderAngularCoefficient f n)
    (continuous_cylinderAngularCoefficient hf n) (cylinderAngularCoefficient_memLp hf hL2 n)
    hmode r
  change ‖cylinderAngularCoefficient f n r‖ ≤
    frequencyL1Norm volume (cylinderFourierMode f hf hL2 n : ℝ → ℂ) at hb
  rw [frequencyL1Norm, toReal_eLpNorm,
    lpNorm_one_eq_integral_norm hmode.aestronglyMeasurable] at hb
  exact hb

/-- Every angular slice has genuinely summable Fourier coefficients. -/
theorem cylinderAngularCoefficient_memLp_one
    (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hL2) 1 cylinderFrequencyMeasure) (r : ℝ) :
    MemLp (fun n : ℤ => cylinderAngularCoefficient f n r) 1 Measure.count := by
  have hi : Integrable (cylinderFourier f hf hL2) (volume.prod Measure.count) :=
    memLp_one_iff_integrable.mp hF1
  apply memLp_one_iff_integrable.mpr
  exact hi.integral_norm_prod_right.mono' (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall (fun n => cylinderAngularCoefficient_norm_le_frequency_integral
      f hf hL2 hF1 n r))

/-- The actual inverse radial transforms reconstruct the original
cylinder function by its ordinary angular Fourier series. -/
theorem cylinder_hasSum_inverse_modes
    (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hL2) 1 cylinderFrequencyMeasure)
    (r : ℝ) (θ : AddCircle P) :
    HasSum (fun n : ℤ => 𝓕⁻ (cylinderFourierMode f hf hL2 n : ℝ → ℂ) r • fourier n θ)
      (f (r, θ)) := by
  let fr : C(AddCircle P, ℂ) :=
    ⟨fun θ => f (r, θ), hf.comp (continuous_const.prodMk continuous_id)⟩
  have hs : Summable (fourierCoeff fr) :=
    (integrable_count_iff.mp (memLp_one_iff_integrable.mp
      (cylinderAngularCoefficient_memLp_one f hf hL2 hF1 r))).of_norm
  have hh := has_pointwise_sum_fourier_series_of_summable hs θ
  have hterms : (fun n : ℤ =>
      𝓕⁻ (cylinderFourierMode f hf hL2 n : ℝ → ℂ) r • fourier n θ) =
      fun n : ℤ => fourierCoeff fr n • fourier n θ := by
    funext n
    rw [cylinderAngularCoefficient_fourierInv f hf hL2 hF1 n]
    rfl
  rw [hterms]
  exact hh

/-- The exact pointwise Fourier `L¹` bound on the full physical cylinder. -/
theorem cylinder_norm_apply_le_fourierL1Norm
    (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hF1 : MemLp (cylinderFourier f hf hL2) 1 cylinderFrequencyMeasure)
    (p : ℝ × AddCircle P) :
    ‖f p‖ ≤ frequencyL1Norm cylinderFrequencyMeasure (cylinderFourier f hf hL2) := by
  let fr : C(AddCircle P, ℂ) :=
    ⟨fun θ => f (p.1, θ), hf.comp (continuous_const.prodMk continuous_id)⟩
  have hslice : MemLp (fourierCoeff fr) 1 Measure.count :=
    cylinderAngularCoefficient_memLp_one f hf hL2 hF1 p.1
  have hi : Integrable (cylinderFourier f hf hL2) (volume.prod Measure.count) :=
    memLp_one_iff_integrable.mp hF1
  calc
    ‖f p‖ ≤ frequencyL1Norm Measure.count (fourierCoeff fr) :=
      circle_norm_apply_le_fourierL1Norm fr hslice p.2
    _ = ∫ n : ℤ, ‖cylinderAngularCoefficient f n p.1‖ ∂Measure.count := by
      rw [frequencyL1Norm, toReal_eLpNorm,
        lpNorm_one_eq_integral_norm hslice.aestronglyMeasurable]
      rfl
    _ ≤ ∫ n : ℤ, (∫ ξ : ℝ, ‖cylinderFourier f hf hL2 (ξ, n)‖) ∂Measure.count :=
      integral_mono (memLp_one_iff_integrable.mp hslice).norm hi.integral_norm_prod_right
        (fun n => cylinderAngularCoefficient_norm_le_frequency_integral f hf hL2 hF1 n p.1)
    _ = ∫ ζ, ‖cylinderFourier f hf hL2 ζ‖ ∂cylinderFrequencyMeasure :=
      (integral_prod_symm _ hi.norm).symm
    _ = frequencyL1Norm cylinderFrequencyMeasure (cylinderFourier f hf hL2) := by
      change (∫ ζ, ‖cylinderFourier f hf hL2 ζ‖ ∂volume.prod Measure.count) =
        frequencyL1Norm (volume.prod Measure.count) (cylinderFourier f hf hL2)
      rw [frequencyL1Norm, toReal_eLpNorm,
        lpNorm_one_eq_integral_norm hi.aestronglyMeasurable]

/-- The physical cylinder `H²` embedding, with the finite inverse-weight
constant depending only on the fixed angular period. -/
theorem cylinder_norm_apply_le_h2
    (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hH2 : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) 2
      (cylinderFourier f hf hL2)) 2 cylinderFrequencyMeasure)
    (p : ℝ × AddCircle P) :
    ‖f p‖ ≤
      (eLpNorm (fun ζ =>
        cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ^ (-2 : ℝ))
        2 cylinderFrequencyMeasure).toReal *
      frequencySobolevNorm cylinderFrequencyMeasure
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) 2
          (cylinderFourier f hf hL2) := by
  have ha : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hq := circlePhysicalFrequencyScale_pos P
  exact (cylinder_norm_apply_le_fourierL1Norm f hf hL2
    (cylinder_frequency_memLp_one_of_h2 ha hq hH2) p).trans
      (cylinder_frequencyL1Norm_le_h2 ha hq hH2)

end ContinuousFlexibility.Analysis
