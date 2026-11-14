module

public import ContinuousFlexibility.Analysis.OneHighCylinderFourierAngular
public import ContinuousFlexibility.Analysis.OneHighCylinderFourierL2Derivative
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Radial differentiation of the actual cylinder Fourier transform

Compactness of the angular circle permits differentiation of its genuine
Fourier coefficient under the integral. The radial `L²` derivative theorem
then supplies the exact physical multiplier on the mixed frequency space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform

variable {P : ℝ} [Fact (0 < P)]

/-- An actual continuous radial derivative passes through the compact
angular Fourier integral. -/
theorem cylinderAngularCoefficient_hasDerivAt
    (f df : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hdf : Continuous df)
    (hderiv : ∀ (θ : AddCircle P) (r : ℝ),
      HasDerivAt (fun y : ℝ => f (y, θ)) (df (r, θ)) r)
    (n : ℤ) (r₀ : ℝ) :
    HasDerivAt (cylinderAngularCoefficient f n) (cylinderAngularCoefficient df n r₀) r₀ := by
  let F (r : ℝ) (θ : AddCircle P) : ℂ := fourier (-n) θ * f (r, θ)
  let F' (r : ℝ) (θ : AddCircle P) : ℂ := fourier (-n) θ * df (r, θ)
  have hF (r : ℝ) : Continuous (F r) :=
    (fourier (-n)).continuous.mul (hf.comp (continuous_const.prodMk continuous_id))
  have hF' (r : ℝ) : Continuous (F' r) :=
    (fourier (-n)).continuous.mul (hdf.comp (continuous_const.prodMk continuous_id))
  have hcompact : IsCompact ((Metric.closedBall r₀ 1) ×ˢ (univ : Set (AddCircle P))) :=
    (isCompact_closedBall r₀ 1).prod isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hdf.continuousOn
  have hint : Integrable (F r₀) AddCircle.haarAddCircle := memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (p := 1) (μ := AddCircle.haarAddCircle) ℂ ⟨F r₀, hF r₀⟩)
  have hbound : ∀ᵐ θ : AddCircle P ∂AddCircle.haarAddCircle,
      ∀ r ∈ Metric.ball r₀ 1, ‖F' r θ‖ ≤ C := by
    exact Eventually.of_forall fun θ r hr => by
      simp only [F', norm_mul, fourier_apply, Circle.norm_coe, one_mul]
      exact hC (r, θ) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hr).le, mem_univ θ⟩
  have hdiff : ∀ᵐ θ : AddCircle P ∂AddCircle.haarAddCircle,
      ∀ r ∈ Metric.ball r₀ 1, HasDerivAt (fun y : ℝ => F y θ) (F' r θ) r :=
    Eventually.of_forall fun θ r _ => (hderiv θ r).const_mul (fourier (-n) θ)
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := AddCircle.haarAddCircle) (F := F) (F' := F') (x₀ := r₀)
    (s := Metric.ball r₀ 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds r₀ (by norm_num))
    (Eventually.of_forall fun r => (hF r).aestronglyMeasurable) hint
    (hF' r₀).aestronglyMeasurable hbound (integrable_const C) hdiff
  change HasDerivAt
    (fun r : ℝ => ∫ θ : AddCircle P, fourier (-n) θ • f (r, θ) ∂AddCircle.haarAddCircle)
    (∫ θ : AddCircle P, fourier (-n) θ • df (r₀, θ) ∂AddCircle.haarAddCircle) r₀
  simpa only [F, F', smul_eq_mul] using hh.2

/-- The exact radial multiplier on every actual radial `L²` Fourier mode. -/
theorem cylinderFourierMode_radialDerivative_ae
    (f df : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hdf : Continuous df)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hdf2 : MemLp df 2 (cylinderPhysicalMeasure P))
    (hderiv : ∀ (θ : AddCircle P) (r : ℝ),
      HasDerivAt (fun y : ℝ => f (y, θ)) (df (r, θ)) r)
    (n : ℤ) :
    (cylinderFourierMode df hdf hdf2 n : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => (2 * Real.pi * Complex.I) * (ξ : ℂ) *
        cylinderFourierMode f hf hf2 n ξ :=
  real_l2_fourier_derivative_ae (cylinderAngularCoefficient f n) (cylinderAngularCoefficient df n)
    (cylinderAngularCoefficient_memLp hf hf2 n) (cylinderAngularCoefficient_memLp hdf hdf2 n)
    (cylinderAngularCoefficient_hasDerivAt f df hf hdf hderiv n)

/-- Radial differentiation multiplies the actual mixed transform by
the physical frequency `2π i ξ`, almost everywhere. -/
theorem cylinderFourier_radialDerivative_ae
    (f df : ℝ × AddCircle P → ℂ) (hf : Continuous f) (hdf : Continuous df)
    (hf2 : MemLp f 2 (cylinderPhysicalMeasure P))
    (hdf2 : MemLp df 2 (cylinderPhysicalMeasure P))
    (hderiv : ∀ (θ : AddCircle P) (r : ℝ),
      HasDerivAt (fun y : ℝ => f (y, θ)) (df (r, θ)) r) :
    cylinderFourier df hdf hdf2 =ᵐ[cylinderFrequencyMeasure]
      fun ζ => ((2 * Real.pi * Complex.I) * (ζ.1 : ℂ)) * cylinderFourier f hf hf2 ζ := by
  have hc : Measurable (fun ζ : ℝ × ℤ =>
      (2 * Real.pi * Complex.I) * (ζ.1 : ℂ)) := by fun_prop
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_cylinderFourier df hdf hdf2)
    (hc.mul (measurable_cylinderFourier f hf hf2)))).mpr
  have hall : ∀ᵐ ξ : ℝ ∂volume, ∀ n : ℤ,
      cylinderFourierMode df hdf hdf2 n ξ =
        (2 * Real.pi * Complex.I) * (ξ : ℂ) * cylinderFourierMode f hf hf2 n ξ :=
    ae_all_iff.mpr (fun n => cylinderFourierMode_radialDerivative_ae
      f df hf hdf hf2 hdf2 hderiv n)
  filter_upwards [hall] with ξ hξ
  exact Eventually.of_forall hξ

end ContinuousFlexibility.Analysis
