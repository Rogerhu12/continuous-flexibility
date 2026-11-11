import ContinuousFlexibility.Radial.ReferenceCosineParseval
import ContinuousFlexibility.Radial.ReferenceCosineAlgebra
import ContinuousFlexibility.Radial.ReferenceWeightedProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Convergence of finite even-cosine projections

The exact angular Parseval identity gives a nonnegative projection error
bounded by the original fiber energy. Dominated convergence for the actual
radial marginal then proves convergence in the frozen weighted Hilbert norm.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
open ContinuousFlexibility.Statements

theorem angularBasisProjection_error_sq {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (I : Finset ℕ) :
    radialAngularMean (fun θ => (angularBasisProjection I f θ - f θ) ^ 2) =
      radialAngularMean (fun θ => f θ ^ 2) -
        ∑ n ∈ I, referenceAngularCoefficient f n ^ 2 := by
  let hF := memLp_referenceAngularProbability hf
  let hP := memLp_referenceAngularProbability
    (memLp_referenceAngular_interval_of_continuous (continuous_angularBasisProjection I f))
  have hnorm :
      radialAngularMean (fun θ => (angularBasisProjection I f θ - f θ) ^ 2) =
        ‖hP.toLp (angularBasisProjection I f) - hF.toLp f‖ ^ 2 := by
    rw [← integral_referenceAngularProbability]
    calc
      (∫ θ, (angularBasisProjection I f θ - f θ) ^ 2 ∂referenceAngularProbability) =
          ‖(hP.sub hF).toLp (angularBasisProjection I f - f)‖ ^ 2 :=
        (reference_memLp_norm_sq_eq_integral (hP.sub hF)).symm
      _ = ‖hP.toLp (angularBasisProjection I f) - hF.toLp f‖ ^ 2 := by
        rw [MemLp.toLp_sub hP hF]
  rw [hnorm, norm_sub_sq_real]
  simp only [reference_memLp_norm_sq_eq_integral hP,
    reference_memLp_norm_sq_eq_integral hF,
    reference_memLp_inner_eq_integral hP hF,
    integral_referenceAngularProbability, angularBasisProjection_sq,
    angularBasisProjection_pairing hf]
  ring

theorem angularBasisProjection_error_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (I : Finset ℕ) :
    radialAngularMean (fun θ => (angularBasisProjection I f θ - f θ) ^ 2) ≤
      radialAngularMean (fun θ => f θ ^ 2) := by
  rw [angularBasisProjection_error_sq hf]
  exact sub_le_self _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem angularCosineProjection_range_eq (N : ℕ) (f : ℝ → ℝ) :
    angularCosineProjection (Finset.range N) f = angularBasisProjection (Finset.range (N + 1)) f := by
  rw [angularCosineProjection_eq_basis]
  congr 1
  ext n
  cases n <;> simp [Finset.mem_image]

theorem angularCosineProjection_error_tendsto {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hp : Function.Periodic f Real.pi) (he : Function.Even f) :
    Tendsto (fun N => radialAngularMean
      (fun θ => (angularCosineProjection (Finset.range N) f θ - f θ) ^ 2)) atTop (𝓝 0) := by
  have hsum := (hasSum_sq_referenceAngularCoefficient hf hp he).tendsto_sum_nat
  have hshift := hsum.comp (tendsto_add_atTop_nat 1)
  have h : Tendsto (fun N => radialAngularMean (fun θ => f θ ^ 2) -
      ∑ n ∈ Finset.range (N + 1), referenceAngularCoefficient f n ^ 2)
      atTop (𝓝 (radialAngularMean (fun θ => f θ ^ 2) -
        radialAngularMean (fun θ => f θ ^ 2))) :=
    tendsto_const_nhds.sub hshift
  simpa only [Function.comp_apply, angularCosineProjection_range_eq,
    angularBasisProjection_error_sq hf, sub_self] using h

theorem memLp_referenceCosineProjection {D : ReferenceData}
    (hD : RadialPartition D) {γ M : ℝ} {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (referenceWeightedMeasure D γ M)) (J : Finset ℕ) :
    MemLp (referenceCosineProjection J u) 2 (referenceWeightedMeasure D γ M) := by
  have hprod := memLp_radial_prod_of_referenceWeighted hD hu
  have hP : MemLp (referenceCosineProjection J u) 2
      ((referenceRadialWeightedMeasure D γ M).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [referenceCosineProjection_eq_basis]
    exact memLp_referenceBasisProjection_prod hprod _
  rw [referenceWeightedMeasure_eq_scaled_radial_prod hD]
  exact hP.smul_measure ENNReal.ofReal_ne_top

/-- Convergence in the actual weighted source field norm. No property of
the border scalar is involved in this angular truncation. -/
theorem referenceCosineProjection_error_tendsto_weighted {D : ReferenceData}
    (hD : RadialPartition D) {γ M : ℝ} {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (referenceWeightedMeasure D γ M))
    (hp : Function.Periodic u (0, Real.pi))
    (he : ∀ r θ, u (r, -θ) = u (r, θ)) :
    Tendsto (fun N => ∫ x,
      (referenceCosineProjection (Finset.range N) u x - u x) ^ 2
        ∂referenceWeightedMeasure D γ M) atTop (𝓝 0) := by
  let E : ℝ → ℝ := fun r => radialAngularMean (fun θ => u (r, θ) ^ 2)
  let e (N : ℕ) (r : ℝ) : ℝ := radialAngularMean
    (fun θ => (referenceCosineProjection (Finset.range N) u (r, θ) - u (r, θ)) ^ 2)
  have hprod := memLp_radial_prod_of_referenceWeighted hD hu
  have hE : Integrable E (referenceRadialWeightedMeasure D γ M) :=
    integrable_radialAngularMean_sq hprod
  have hPN (N : ℕ) := memLp_referenceCosineProjection hD hu (Finset.range N)
  have heI (N : ℕ) : Integrable (e N) (referenceRadialWeightedMeasure D γ M) :=
    integrable_radialAngularMean_sq
      (memLp_radial_prod_of_referenceWeighted hD ((hPN N).sub hu))
  have hbound (N : ℕ) : ∀ᵐ r ∂referenceRadialWeightedMeasure D γ M, ‖e N r‖ ≤ E r := by
    filter_upwards [memLp_two_prod_sections hprod] with r hr
    have hnonneg : 0 ≤ e N r := by
      rw [show e N r = ∫ θ,
        (referenceCosineProjection (Finset.range N) u (r, θ) - u (r, θ)) ^ 2
          ∂referenceAngularProbability from (integral_referenceAngularProbability _).symm]
      exact integral_nonneg (fun _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnonneg]
    change radialAngularMean
      (fun θ => (angularCosineProjection (Finset.range N) (fun θ => u (r, θ)) θ -
        u (r, θ)) ^ 2) ≤ _
    rw [angularCosineProjection_range_eq]
    exact angularBasisProjection_error_sq_le hr _
  have hlimit : ∀ᵐ r ∂referenceRadialWeightedMeasure D γ M,
      Tendsto (fun N => e N r) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [memLp_two_prod_sections hprod] with r hr
    apply angularCosineProjection_error_tendsto hr
    · intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hp (r, θ)
    · exact he r
  have ht := tendsto_integral_of_dominated_convergence E
    (fun N => (heI N).aestronglyMeasurable) hE hbound hlimit
  have heq (N : ℕ) :
      (∫ x, (referenceCosineProjection (Finset.range N) u x - u x) ^ 2
        ∂referenceWeightedMeasure D γ M) =
      ∫ r, e N r ∂referenceRadialWeightedMeasure D γ M :=
    integral_referenceWeightedMeasure_eq_radial hD ((hPN N).sub hu).integrable_sq
  simpa only [heq, integral_zero] using ht

theorem referenceCosineProjection_tendsto_L2 {D : ReferenceData}
    (hD : RadialPartition D) {γ M : ℝ} {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (referenceWeightedMeasure D γ M))
    (hp : Function.Periodic u (0, Real.pi))
    (he : ∀ r θ, u (r, -θ) = u (r, θ)) :
    Tendsto (fun N => (memLp_referenceCosineProjection hD hu (Finset.range N)).toLp
      (referenceCosineProjection (Finset.range N) u)) atTop (𝓝 (hu.toLp u)) := by
  exact reference_memLp_tendsto_of_sub_sq
    (fun N => memLp_referenceCosineProjection hD hu (Finset.range N)) hu
    (referenceCosineProjection_error_tendsto_weighted hD hu hp he)

end ContinuousFlexibility.Radial
