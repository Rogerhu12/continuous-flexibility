module

public import ContinuousFlexibility.Analysis.OneHighCylinderPlancherel

/-!
# Converse angular Parseval on the full cylinder

For every continuous cylinder function, angular Parseval and Tonelli
identify its extended L2 norm with that of all angular coefficients.
Square integrability of the function is a conclusion when the coefficient
energy, or equivalently the energy of their real Fourier transforms, is finite.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform

variable {P : ℝ} [Fact (0 < P)]

def cylinderAngularFourier (f : ℝ × AddCircle P → ℂ) (ζ : ℝ × ℤ) : ℂ :=
  cylinderAngularCoefficient f ζ.2 ζ.1

theorem measurable_cylinderAngularFourier {f : ℝ × AddCircle P → ℂ}
    (hf : Continuous f) : Measurable (cylinderAngularFourier f) :=
  measurable_from_prod_countable_left fun n => (continuous_cylinderAngularCoefficient hf n).measurable

private theorem eLpNorm_two_sq_angular {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa [ENNReal.rpow_two] using
    eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf

private theorem eLpNorm_two_sqrt_angular {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf

theorem cylinderAngularFourier_lintegral_sq {f : ℝ × AddCircle P → ℂ}
    (hf : Continuous f) :
    (∫⁻ ζ, ‖cylinderAngularFourier f ζ‖ₑ ^ 2 ∂cylinderFrequencyMeasure) =
      ∫⁻ p, ‖f p‖ₑ ^ 2 ∂cylinderPhysicalMeasure P := by
  have hm := (measurable_cylinderAngularFourier hf).enorm.pow_const (2 : ℕ)
  have hangular (r : ℝ) :
      (∫⁻ n : ℤ, ‖cylinderAngularCoefficient f n r‖ₑ ^ 2 ∂Measure.count) =
        ∫⁻ θ : AddCircle P, ‖f (r, θ)‖ₑ ^ 2 ∂AddCircle.haarAddCircle := by
    let fr : C(AddCircle P, ℂ) :=
      ⟨fun θ => f (r, θ), hf.comp (continuous_const.prodMk continuous_id)⟩
    exact circle_lintegral_sq_fourierCoeff
      (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ fr)
  calc
    _ = ∫⁻ r : ℝ, ∫⁻ n : ℤ, ‖cylinderAngularCoefficient f n r‖ₑ ^ 2 ∂Measure.count :=
      lintegral_prod _ hm.aemeasurable
    _ = ∫⁻ r : ℝ, ∫⁻ θ : AddCircle P, ‖f (r, θ)‖ₑ ^ 2 ∂AddCircle.haarAddCircle :=
      lintegral_congr hangular
    _ = _ := (lintegral_prod _ (hf.measurable.enorm.pow_const (2 : ℕ)).aemeasurable).symm

theorem cylinderAngularFourier_eLpNorm_two {f : ℝ × AddCircle P → ℂ}
    (hf : Continuous f) :
    eLpNorm (cylinderAngularFourier f) 2 cylinderFrequencyMeasure =
      eLpNorm f 2 (cylinderPhysicalMeasure P) := by
  rw [eLpNorm_two_sqrt_angular (measurable_cylinderAngularFourier hf).aestronglyMeasurable,
    eLpNorm_two_sqrt_angular hf.aestronglyMeasurable,
    cylinderAngularFourier_lintegral_sq hf]

theorem cylinder_memLp_two_of_angularFourier {f : ℝ × AddCircle P → ℂ}
    (hf : Continuous f) (hcoeff : MemLp (cylinderAngularFourier f) 2 cylinderFrequencyMeasure) :
    MemLp f 2 (cylinderPhysicalMeasure P) := by
  rw [memLp_iff, ← cylinderAngularFourier_eLpNorm_two hf]
  exact hcoeff

theorem cylinderFrequency_slice_memLp_two_of_measurable {M : ℝ × ℤ → ℂ}
    (hM : Measurable M) (hM2 : MemLp M 2 cylinderFrequencyMeasure) (n : ℤ) :
    MemLp (fun ξ : ℝ => M (ξ, n)) 2 (volume : Measure ℝ) := by
  have hi : Integrable (fun ζ : ℝ × ℤ => ‖M ζ‖ ^ 2) (volume.prod Measure.count) :=
    hM2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  exact (memLp_two_iff_integrable_sq_norm
    (hM.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr
      (Measure.ae_count_iff.mp hi.prod_left_ae n)

/-- Finiteness of a family of actual real Fourier modes implies physical
L2 membership, with the exact extended norm equality. -/
theorem cylinder_eLpNorm_two_of_fourier_modes
    (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (M : ℝ × ℤ → ℂ) (hM : Measurable M) (hM2 : MemLp M 2 cylinderFrequencyMeasure)
    (hc : ∀ n : ℤ, MemLp (cylinderAngularCoefficient f n) 2 (volume : Measure ℝ))
    (he : ∀ n : ℤ,
      ((𝓕 ((hc n).toLp (cylinderAngularCoefficient f n)) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] fun ξ => M (ξ, n)) :
    eLpNorm f 2 (cylinderPhysicalMeasure P) = eLpNorm M 2 cylinderFrequencyMeasure := by
  have hmodes (n : ℤ) :
      (∫⁻ r : ℝ, ‖cylinderAngularCoefficient f n r‖ₑ ^ 2) =
        ∫⁻ ξ : ℝ, ‖M (ξ, n)‖ₑ ^ 2 := by
    have hn2 := cylinderFrequency_slice_memLp_two_of_measurable hM hM2 n
    have hn : eLpNorm (cylinderAngularCoefficient f n) 2 (volume : Measure ℝ) =
        eLpNorm (fun ξ : ℝ => M (ξ, n)) 2 (volume : Measure ℝ) := by
      apply (ENNReal.toReal_eq_toReal_iff' (hc n).ne hn2.ne).mp
      calc
        _ = ‖(hc n).toLp (cylinderAngularCoefficient f n)‖ := (Lp.norm_toLp _ _).symm
        _ = ‖𝓕 ((hc n).toLp (cylinderAngularCoefficient f n))‖ :=
          (Lp.norm_fourier_eq _).symm
        _ = _ := (Lp.norm_def _).trans (congrArg ENNReal.toReal (eLpNorm_congr_ae (he n)))
    rw [← eLpNorm_two_sq_angular (hc n).aestronglyMeasurable,
      ← eLpNorm_two_sq_angular hn2.aestronglyMeasurable, hn]
  have hsq : (∫⁻ ζ, ‖cylinderAngularFourier f ζ‖ₑ ^ 2 ∂cylinderFrequencyMeasure) =
      ∫⁻ ζ, ‖M ζ‖ₑ ^ 2 ∂cylinderFrequencyMeasure := by
    calc
      _ = ∫⁻ n : ℤ, (∫⁻ r : ℝ, ‖cylinderAngularCoefficient f n r‖ₑ ^ 2) ∂Measure.count :=
        lintegral_prod_symm _
          ((measurable_cylinderAngularFourier hf).enorm.pow_const (2 : ℕ)).aemeasurable
      _ = ∫⁻ n : ℤ, (∫⁻ ξ : ℝ, ‖M (ξ, n)‖ₑ ^ 2) ∂Measure.count :=
        lintegral_congr hmodes
      _ = _ := (lintegral_prod_symm _ (hM.enorm.pow_const (2 : ℕ)).aemeasurable).symm
  rw [← cylinderAngularFourier_eLpNorm_two hf,
    eLpNorm_two_sqrt_angular (measurable_cylinderAngularFourier hf).aestronglyMeasurable,
    eLpNorm_two_sqrt_angular hM.aestronglyMeasurable, hsq]

theorem cylinder_memLp_two_of_fourier_modes
    (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (M : ℝ × ℤ → ℂ) (hM : Measurable M) (hM2 : MemLp M 2 cylinderFrequencyMeasure)
    (hc : ∀ n : ℤ, MemLp (cylinderAngularCoefficient f n) 2 (volume : Measure ℝ))
    (he : ∀ n : ℤ,
      ((𝓕 ((hc n).toLp (cylinderAngularCoefficient f n)) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] fun ξ => M (ξ, n)) :
    MemLp f 2 (cylinderPhysicalMeasure P) := by
  rw [memLp_iff, cylinder_eLpNorm_two_of_fourier_modes f hf M hM hM2 hc he]
  exact hM2

end ContinuousFlexibility.Analysis
