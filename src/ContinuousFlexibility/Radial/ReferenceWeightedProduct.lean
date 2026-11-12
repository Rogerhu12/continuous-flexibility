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
    SFinite (referenceWeightedMeasure D γ M) :=
  ContinuousFlexibility.Statements.referenceWeightedMeasure_sFinite D γ M

instance referenceRadialWeightedMeasure_sFinite (D : ReferenceData) (γ M : ℝ) :
    SFinite (referenceRadialWeightedMeasure D γ M) :=
  ContinuousFlexibility.Statements.referenceRadialWeightedMeasure_sFinite D γ M

instance referenceAngularProbability_isProbability :
    IsProbabilityMeasure referenceAngularProbability :=
  ContinuousFlexibility.Statements.referenceAngularMeasure_probability

/-- Both public radial APIs refer to the same physical marginal and use
the already proved cell-product representation. -/
theorem referenceWeightedMeasure_eq_radial_prod {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) :
    referenceWeightedMeasure D γ M =
      (referenceRadialWeightedMeasure D γ M).prod referenceAngularProbability :=
  ContinuousFlexibility.Statements.referenceWeightedMeasure_eq_prod hD γ M

theorem referenceWeightedMeasure_eq_scaled_radial_prod {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) :
    referenceWeightedMeasure D γ M = ENNReal.ofReal ((2 * Real.pi)⁻¹) •
      (referenceRadialWeightedMeasure D γ M).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  rw [referenceWeightedMeasure_eq_radial_prod hD, referenceAngularProbability,
    referenceAngularMeasure, Measure.prod_smul_right]

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
