import ContinuousFlexibility.Analysis.OneHighCylinderPlancherel
import ContinuousFlexibility.Analysis.OneHighCircleFourierDerivative

/-!
# Angular differentiation of the actual cylinder Fourier transform

The circle integration-by-parts identity holds on each physical radial
slice. Passing that identity through the genuine radial `L²` Fourier
isometry gives the physical angular multiplier almost everywhere on the
full mixed frequency space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal FourierTransform

variable {P : ℝ} [Fact (0 < P)]

theorem cylinderAngularCoefficient_of_hasDerivAt
    (f df : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hdf : Continuous df)
    (hderiv : ∀ r x : ℝ,
      HasDerivAt (fun y : ℝ => f (r, (y : AddCircle P)))
        (df (r, (x : AddCircle P))) x)
    (n : ℤ) (r : ℝ) :
    cylinderAngularCoefficient df n r =
      (Complex.I * (circlePhysicalFrequency P n : ℂ)) *
        cylinderAngularCoefficient f n r := by
  let fr : C(AddCircle P, ℂ) :=
    ⟨fun θ => f (r, θ), hf.comp (continuous_const.prodMk continuous_id)⟩
  let dfr : C(AddCircle P, ℂ) :=
    ⟨fun θ => df (r, θ), hdf.comp (continuous_const.prodMk continuous_id)⟩
  exact circle_fourierCoeff_of_hasDerivAt fr dfr (hderiv r) n

/-- Angular differentiation commutes with the actual radial `L²`
Fourier isometry, with its exact physical multiplier. -/
theorem cylinderFourierMode_angularDerivative
    (f df : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hdf : Continuous df)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hdf2 : MemLp df 2 (cylinderPhysicalMeasure P))
    (hderiv : ∀ r x : ℝ,
      HasDerivAt (fun y : ℝ => f (r, (y : AddCircle P)))
        (df (r, (x : AddCircle P))) x)
    (n : ℤ) :
    cylinderFourierMode df hdf hdf2 n =
      (Complex.I * (circlePhysicalFrequency P n : ℂ)) • cylinderFourierMode f hf hf2 n := by
  let c : ℂ := Complex.I * (circlePhysicalFrequency P n : ℂ)
  have hcf := cylinderAngularCoefficient_memLp hf hf2 n
  have hcdf := cylinderAngularCoefficient_memLp hdf hdf2 n
  have he : cylinderAngularCoefficient df n =ᵐ[volume] c • cylinderAngularCoefficient f n :=
    Eventually.of_forall (fun r => cylinderAngularCoefficient_of_hasDerivAt
      f df hf hdf hderiv n r)
  have hl := hcdf.toLp_congr (hcf.const_smul c) he
  rw [MemLp.toLp_const_smul] at hl
  unfold cylinderFourierMode
  rw [hl, FourierTransform.fourier_smul]

theorem cylinderFourierMode_angularDerivative_ae
    (f df : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hdf : Continuous df)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hdf2 : MemLp df 2 (cylinderPhysicalMeasure P))
    (hderiv : ∀ r x : ℝ,
      HasDerivAt (fun y : ℝ => f (r, (y : AddCircle P)))
        (df (r, (x : AddCircle P))) x)
    (n : ℤ) :
    (cylinderFourierMode df hdf hdf2 n : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (Complex.I * (circlePhysicalFrequency P n : ℂ)) *
        cylinderFourierMode f hf hf2 n ξ := by
  rw [cylinderFourierMode_angularDerivative f df hf hdf hf2 hdf2 hderiv n]
  exact Lp.coeFn_smul _ _

/-- The derivative multiplier identity on the entire mixed frequency
measure, with no auxiliary integrability assumption on radial slices. -/
theorem cylinderFourier_angularDerivative_ae
    (f df : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hdf : Continuous df)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hdf2 : MemLp df 2 (cylinderPhysicalMeasure P))
    (hderiv : ∀ r x : ℝ,
      HasDerivAt (fun y : ℝ => f (r, (y : AddCircle P)))
        (df (r, (x : AddCircle P))) x) :
    cylinderFourier df hdf hdf2 =ᵐ[cylinderFrequencyMeasure]
      fun ζ => (Complex.I * (circlePhysicalFrequency P ζ.2 : ℂ)) *
        cylinderFourier f hf hf2 ζ := by
  have hc : Measurable (fun ζ : ℝ × ℤ =>
      Complex.I * (circlePhysicalFrequency P ζ.2 : ℂ)) :=
    (measurable_of_countable (fun n : ℤ =>
      Complex.I * (circlePhysicalFrequency P n : ℂ))).comp measurable_snd
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_cylinderFourier df hdf hdf2)
    (hc.mul (measurable_cylinderFourier f hf hf2)))).mpr
  have hall : ∀ᵐ ξ : ℝ ∂volume, ∀ n : ℤ,
      cylinderFourierMode df hdf hdf2 n ξ =
        (Complex.I * (circlePhysicalFrequency P n : ℂ)) *
          cylinderFourierMode f hf hf2 n ξ :=
    ae_all_iff.mpr (fun n => cylinderFourierMode_angularDerivative_ae
      f df hf hdf hf2 hdf2 hderiv n)
  filter_upwards [hall] with ξ hξ
  exact Eventually.of_forall hξ

end ContinuousFlexibility.Analysis
