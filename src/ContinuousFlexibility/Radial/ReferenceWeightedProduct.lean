import ContinuousFlexibility.Radial.ReferenceWeightedCompact
import ContinuousFlexibility.Radial.ReferenceCosineCoefficients
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Exact product disintegration of the reference weight

The radial marginal of the frozen weighted physical measure and normalized
angular measure reconstruct the same measure exactly. This supplies
Fubini and L² estimates for the actual radial Fourier coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ENNReal
open ContinuousFlexibility.Statements

instance referenceWeightedMeasure_sFinite (D : ReferenceData) (γ M : ℝ) :
    SFinite (referenceWeightedMeasure D γ M) := by
  unfold referenceWeightedMeasure referenceWeightedCellMeasure radialPhysicalMeasure
  infer_instance

instance referenceRadialWeightedMeasure_sFinite (D : ReferenceData) (γ M : ℝ) :
    SFinite (referenceRadialWeightedMeasure D γ M) := by
  unfold referenceRadialWeightedMeasure
  infer_instance

instance referenceAngularProbability_isProbability :
    IsProbabilityMeasure referenceAngularProbability := by
  constructor
  rw [referenceAngularProbability, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

/-- The canonical weighted measure is the product of its radial marginal
and the probability measure on the same physical angular period. -/
theorem referenceWeightedMeasure_eq_radial_prod {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) :
    referenceWeightedMeasure D γ M =
      (referenceRadialWeightedMeasure D γ M).prod referenceAngularProbability := by
  let ρ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let d (m : ℕ) (r : ℝ) : ℝ≥0∞ :=
    ENNReal.ofReal (referenceCellMeasureWeight D γ M m * D.localizer m r ^ 2)
  let ν : Measure ℝ :=
    Measure.sum (fun m => (volume.restrict (radialCore D)).withDensity (d m))
  have hd (m : ℕ) : Measurable (d m) :=
    (measurable_const.mul ((hD.1 m).continuous.measurable.pow_const 2)).ennreal_ofReal
  have hprod : referenceWeightedMeasure D γ M = ν.prod ρ := by
    rw [show ν.prod ρ = Measure.sum
      (fun m => ((volume.restrict (radialCore D)).withDensity (d m)).prod ρ)
      from Measure.prod_sum_left _ _]
    unfold referenceWeightedMeasure
    congr 1
    funext m
    rw [prod_withDensity_left (hd m), ← radialPhysicalMeasure_eq_prod]
    rfl
  have hmass : ρ univ = ENNReal.ofReal (2 * Real.pi) := by
    simp only [ρ, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  have hcancel :
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal ((2 * Real.pi)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
      ENNReal.ofReal_one]
  unfold referenceRadialWeightedMeasure
  rw [hprod, Measure.map_fst_prod, referenceAngularProbability, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, hmass, hcancel, one_smul]

theorem referenceWeightedMeasure_eq_scaled_radial_prod {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) :
    referenceWeightedMeasure D γ M = ENNReal.ofReal ((2 * Real.pi)⁻¹) •
      (referenceRadialWeightedMeasure D γ M).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  rw [referenceWeightedMeasure_eq_radial_prod hD, referenceAngularProbability,
    Measure.prod_smul_right]

theorem memLp_radial_prod_of_referenceWeighted {D : ReferenceData}
    (hD : RadialPartition D) {γ M : ℝ} {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (referenceWeightedMeasure D γ M)) :
    MemLp u 2 ((referenceRadialWeightedMeasure D γ M).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  rw [referenceWeightedMeasure_eq_scaled_radial_prod hD] at hu
  have h := hu.smul_measure (c := (ENNReal.ofReal ((2 * Real.pi)⁻¹))⁻¹) (by finiteness)
  rwa [smul_smul, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top,
    one_smul] at h

theorem memLp_referenceRadialCoefficient {D : ReferenceData}
    (hD : RadialPartition D) {γ M : ℝ} {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (referenceWeightedMeasure D γ M)) (n : ℕ) :
    MemLp (referenceRadialCoefficient u n) 2 (referenceRadialWeightedMeasure D γ M) :=
  memLp_referenceRadialCoefficient_prod (memLp_radial_prod_of_referenceWeighted hD hu) n

theorem integral_referenceWeightedMeasure_eq_radial {D : ReferenceData}
    (hD : RadialPartition D) {γ M : ℝ} {f : PolarPoint → ℝ}
    (hf : Integrable f (referenceWeightedMeasure D γ M)) :
    (∫ x, f x ∂referenceWeightedMeasure D γ M) =
      ∫ r, radialAngularMean (fun θ => f (r, θ)) ∂referenceRadialWeightedMeasure D γ M := by
  rw [referenceWeightedMeasure_eq_radial_prod hD] at hf ⊢
  rw [integral_prod _ hf]
  exact integral_congr_ae (ae_of_all _ (fun r =>
    integral_referenceAngularProbability (fun θ => f (r, θ))))

theorem integral_referenceRadialCoefficient_sq_le {D : ReferenceData}
    (hD : RadialPartition D) {γ M : ℝ} {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (referenceWeightedMeasure D γ M)) (n : ℕ) :
    (∫ r, referenceRadialCoefficient u n r ^ 2 ∂referenceRadialWeightedMeasure D γ M) ≤
      ∫ x, u x ^ 2 ∂referenceWeightedMeasure D γ M := by
  have h := integral_referenceRadialCoefficient_sq_le_prod
    (memLp_radial_prod_of_referenceWeighted hD hu) n
  rw [referenceWeightedMeasure_eq_scaled_radial_prod hD, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  exact h

end ContinuousFlexibility.Radial
