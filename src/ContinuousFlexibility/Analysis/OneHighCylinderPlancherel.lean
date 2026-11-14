module

public import ContinuousFlexibility.Analysis.OneHighCylinderCoefficients
public import ContinuousFlexibility.Analysis.OneHighCylinderFrequency

/-!
# Plancherel for the actual cylinder Fourier transform

Circle Parseval is applied to every continuous angular slice. Tonelli then
interchanges the real and integer frequency variables, and the genuine radial
`L²` Fourier isometry preserves each angular mode. All frequency membership is
obtained from square integrability of the original physical function.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal NNReal

private theorem eLpNorm_two_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa [ENNReal.rpow_two] using
    eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf

private theorem eLpNorm_two_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf

variable {P : ℝ} [Fact (0 < P)]

/-- The circle Parseval identity before conversion to real norms. -/
theorem circle_lintegral_sq_fourierCoeff {f : AddCircle P → ℂ}
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    (∫⁻ n : ℤ, ‖fourierCoeff f n‖ₑ ^ 2 ∂Measure.count) =
      ∫⁻ θ, ‖f θ‖ₑ ^ 2 ∂AddCircle.haarAddCircle := by
  have hfc := circle_fourier_memLp_two_of_memLp hf
  have hn : eLpNorm (fourierCoeff f) 2 Measure.count =
      eLpNorm f 2 AddCircle.haarAddCircle := by
    apply (ENNReal.toReal_eq_toReal_iff' hfc.ne hf.ne).mp
    simpa only [frequencySobolevNorm, frequencyWeighted_zero] using
      circle_frequencySobolevNorm_zero_eq_l2 hf
  rw [← eLpNorm_two_sq hfc.aestronglyMeasurable,
    ← eLpNorm_two_sq hf.aestronglyMeasurable, hn]

/-- The chosen representatives of the radial `L²` Fourier modes give a
measurable function on the complete mixed frequency space. -/
theorem measurable_cylinderFourier (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) : Measurable (cylinderFourier f hf hL2) :=
  measurable_from_prod_countable_left fun n =>
    (Lp.stronglyMeasurable (cylinderFourierMode f hf hL2 n)).measurable

private theorem cylinderFourierMode_lintegral_sq (f : ℝ × AddCircle P → ℂ)
    (hf : Continuous f) (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) (n : ℤ) :
    (∫⁻ r : ℝ, ‖cylinderFourierMode f hf hL2 n r‖ₑ ^ 2) =
      ∫⁻ r : ℝ, ‖cylinderAngularCoefficient f n r‖ₑ ^ 2 := by
  have hn : eLpNorm (cylinderFourierMode f hf hL2 n) 2 (volume : Measure ℝ) =
      eLpNorm (cylinderAngularCoefficient f n) 2 (volume : Measure ℝ) := by
    apply (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _)
      (cylinderAngularCoefficient_memLp hf hL2 n).ne).mp
    exact (Lp.norm_def _).symm.trans (norm_cylinderFourierMode f hf hL2 n)
  rw [← eLpNorm_two_sq (Lp.aestronglyMeasurable (cylinderFourierMode f hf hL2 n)),
    ← eLpNorm_two_sq (continuous_cylinderAngularCoefficient hf n).aestronglyMeasurable, hn]

/-- The mixed transform preserves the full squared integral, as an
identity of extended nonnegative real numbers. -/
theorem cylinderFourier_lintegral_sq (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) :
    (∫⁻ ζ, ‖cylinderFourier f hf hL2 ζ‖ₑ ^ 2 ∂cylinderFrequencyMeasure) =
      ∫⁻ p, ‖f p‖ₑ ^ 2 ∂cylinderPhysicalMeasure P := by
  have hF : Measurable (fun ζ : ℝ × ℤ => cylinderAngularCoefficient f ζ.2 ζ.1) :=
    measurable_from_prod_countable_left fun n => (continuous_cylinderAngularCoefficient hf n).measurable
  have hfm := (measurable_cylinderFourier f hf hL2).enorm.pow_const (2 : ℕ)
  have hFm := hF.enorm.pow_const (2 : ℕ)
  have hangular (r : ℝ) :
      (∫⁻ n : ℤ, ‖cylinderAngularCoefficient f n r‖ₑ ^ 2 ∂Measure.count) =
        ∫⁻ θ : AddCircle P, ‖f (r, θ)‖ₑ ^ 2 ∂AddCircle.haarAddCircle := by
    let fr : C(AddCircle P, ℂ) :=
      ⟨fun θ => f (r, θ), hf.comp (continuous_const.prodMk continuous_id)⟩
    exact circle_lintegral_sq_fourierCoeff
      (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ fr)
  calc
    _ = ∫⁻ n : ℤ, (∫⁻ r : ℝ, ‖cylinderFourierMode f hf hL2 n r‖ₑ ^ 2) ∂Measure.count :=
      lintegral_prod_symm _ hfm.aemeasurable
    _ = ∫⁻ n : ℤ, (∫⁻ r : ℝ, ‖cylinderAngularCoefficient f n r‖ₑ ^ 2) ∂Measure.count :=
      lintegral_congr fun n => cylinderFourierMode_lintegral_sq f hf hL2 n
    _ = ∫⁻ ζ : ℝ × ℤ, ‖cylinderAngularCoefficient f ζ.2 ζ.1‖ₑ ^ 2
        ∂cylinderFrequencyMeasure := (lintegral_prod_symm _ hFm.aemeasurable).symm
    _ = ∫⁻ r : ℝ, ∫⁻ n : ℤ, ‖cylinderAngularCoefficient f n r‖ₑ ^ 2 ∂Measure.count :=
      lintegral_prod _ hFm.aemeasurable
    _ = ∫⁻ r : ℝ, ∫⁻ θ : AddCircle P, ‖f (r, θ)‖ₑ ^ 2 ∂AddCircle.haarAddCircle :=
      lintegral_congr hangular
    _ = _ := (lintegral_prod _ (hf.measurable.enorm.pow_const (2 : ℕ)).aemeasurable).symm

/-- The exact extended `L²` norm equality for the actual mixed transform. -/
theorem cylinderFourier_eLpNorm_two (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) :
    eLpNorm (cylinderFourier f hf hL2) 2 cylinderFrequencyMeasure =
      eLpNorm f 2 (cylinderPhysicalMeasure P) := by
  rw [eLpNorm_two_sqrt (measurable_cylinderFourier f hf hL2).aestronglyMeasurable,
    eLpNorm_two_sqrt hf.aestronglyMeasurable, cylinderFourier_lintegral_sq f hf hL2]

theorem cylinderFourier_memLp_two (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) :
    MemLp (cylinderFourier f hf hL2) 2 cylinderFrequencyMeasure := by
  rw [memLp_iff, cylinderFourier_eLpNorm_two f hf hL2]
  exact hL2

/-- The cylinder frequency `H⁰` norm is the physical cylinder `L²` norm. -/
theorem cylinder_frequencySobolevNorm_zero_eq_l2 (f : ℝ × AddCircle P → ℂ)
    (hf : Continuous f) (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) :
    frequencySobolevNorm cylinderFrequencyMeasure
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) 0
        (cylinderFourier f hf hL2) = (eLpNorm f 2 (cylinderPhysicalMeasure P)).toReal := by
  rw [frequencySobolevNorm, frequencyWeighted_zero, cylinderFourier_eLpNorm_two f hf hL2]

end ContinuousFlexibility.Analysis
