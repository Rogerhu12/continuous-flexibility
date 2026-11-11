import ContinuousFlexibility.Analysis.OneHighCylinderAngularPlancherel
import ContinuousFlexibility.Analysis.OneHighCylinderFourierL2ReverseDerivative
import ContinuousFlexibility.Analysis.OneHighCylinderFourierRadial

/-!
# Actual cylinder derivatives from frequency membership

The radial argument applies the reverse real derivative theorem to every
angular coefficient. The angular argument uses the exact coefficient
multiplier. Converse Parseval then proves full physical L2 membership,
without assuming it for either actual derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal FourierTransform

variable {P : ℝ} [Fact (0 < P)]

theorem cylinder_memLp_radialDerivative_of_frequency
    (f df : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hdf : Continuous df)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hderiv : ∀ (θ : AddCircle P) (r : ℝ),
      HasDerivAt (fun y : ℝ => f (y, θ)) (df (r, θ)) r)
    (hM2 : MemLp (fun ζ : ℝ × ℤ =>
      (2 * Real.pi * Complex.I) * (ζ.1 : ℂ) * cylinderFourier f hf hf2 ζ)
        2 cylinderFrequencyMeasure) :
    MemLp df 2 (cylinderPhysicalMeasure P) := by
  let M : ℝ × ℤ → ℂ := fun ζ =>
    (2 * Real.pi * Complex.I) * (ζ.1 : ℂ) * cylinderFourier f hf hf2 ζ
  have hM : Measurable M := by
    exact (show Measurable (fun ζ : ℝ × ℤ =>
      (2 * Real.pi * Complex.I) * (ζ.1 : ℂ)) by fun_prop).mul
        (measurable_cylinderFourier f hf hf2)
  have hc (n : ℤ) : MemLp (cylinderAngularCoefficient df n) 2 (volume : Measure ℝ) :=
    real_memLp_derivative_of_frequency (cylinderAngularCoefficient f n)
      (cylinderAngularCoefficient df n) (cylinderAngularCoefficient_memLp hf hf2 n)
      (continuous_cylinderAngularCoefficient hdf n)
      (cylinderAngularCoefficient_hasDerivAt f df hf hdf hderiv n)
      (cylinderFrequency_slice_memLp_two_of_measurable hM hM2 n)
  have he (n : ℤ) :
      ((𝓕 ((hc n).toLp (cylinderAngularCoefficient df n)) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] fun ξ => M (ξ, n) :=
    real_l2_fourier_derivative_ae (cylinderAngularCoefficient f n)
      (cylinderAngularCoefficient df n) (cylinderAngularCoefficient_memLp hf hf2 n) (hc n)
      (cylinderAngularCoefficient_hasDerivAt f df hf hdf hderiv n)
  exact cylinder_memLp_two_of_fourier_modes df hdf M hM hM2 hc he

theorem cylinder_memLp_angularDerivative_of_frequency
    (f df : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hdf : Continuous df)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hderiv : ∀ r x : ℝ,
      HasDerivAt (fun y : ℝ => f (r, (y : AddCircle P)))
        (df (r, (x : AddCircle P))) x)
    (hM2 : MemLp (fun ζ : ℝ × ℤ =>
      (Complex.I * (circlePhysicalFrequency P ζ.2 : ℂ)) * cylinderFourier f hf hf2 ζ)
        2 cylinderFrequencyMeasure) :
    MemLp df 2 (cylinderPhysicalMeasure P) := by
  let c (n : ℤ) : ℂ := Complex.I * (circlePhysicalFrequency P n : ℂ)
  let M : ℝ × ℤ → ℂ := fun ζ => c ζ.2 * cylinderFourier f hf hf2 ζ
  have hM : Measurable M :=
    ((measurable_of_countable c).comp measurable_snd).mul
      (measurable_cylinderFourier f hf hf2)
  have heq (n : ℤ) : cylinderAngularCoefficient df n = c n • cylinderAngularCoefficient f n := by
    funext r
    exact cylinderAngularCoefficient_of_hasDerivAt f df hf hdf hderiv n r
  have hc (n : ℤ) : MemLp (cylinderAngularCoefficient df n) 2 (volume : Measure ℝ) := by
    rw [heq n]
    exact (cylinderAngularCoefficient_memLp hf hf2 n).const_smul (c n)
  have he (n : ℤ) :
      ((𝓕 ((hc n).toLp (cylinderAngularCoefficient df n)) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] fun ξ => M (ξ, n) := by
    have hcf := cylinderAngularCoefficient_memLp hf hf2 n
    have ht : cylinderAngularCoefficient df n =ᵐ[volume]
        c n • cylinderAngularCoefficient f n := Eventually.of_forall (congrFun (heq n))
    have hl := (hc n).toLp_congr (hcf.const_smul (c n)) ht
    rw [MemLp.toLp_const_smul (c n) hcf] at hl
    rw [hl, FourierTransform.fourier_smul]
    exact Lp.coeFn_smul _ _
  exact cylinder_memLp_two_of_fourier_modes df hdf M hM hM2 hc he

end ContinuousFlexibility.Analysis
