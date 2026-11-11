import ContinuousFlexibility.Radial.ReferenceWeightedMeasure

/-!
# Product structure of the actual weighted reference measure

The radial weights are independent of the angular variable. Moving the
normalization into the angular measure expresses the Hilbert realization
as the product of the actual weighted radial measure and normalized
Lebesgue measure on one full angular period.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal

def referenceAngularMeasure : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) •
    volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

instance referenceAngularMeasure_probability : IsProbabilityMeasure referenceAngularMeasure where
  measure_univ := by
    simp only [referenceAngularMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
      Real.volume_Ioc, sub_zero, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹),
      inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), ENNReal.ofReal_one]

theorem integral_referenceAngularMeasure (f : ℝ → ℝ) :
    (∫ θ, f θ ∂referenceAngularMeasure) = radialAngularMean f := by
  unfold referenceAngularMeasure radialAngularMean
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]

def referenceRadialCellDensity (D : ReferenceData) (γ M : ℝ) (m : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
      (D.localizer m r) ^ 2)

def referenceRadialWeightedCellMeasure (D : ReferenceData) (γ M : ℝ) (m : ℕ) : Measure ℝ :=
  (volume.restrict (radialCore D)).withDensity (referenceRadialCellDensity D γ M m)

def referenceRadialWeightedMeasure (D : ReferenceData) (γ M : ℝ) : Measure ℝ :=
  Measure.sum (referenceRadialWeightedCellMeasure D γ M)

instance referenceRadialWeightedCellMeasure_sFinite (D : ReferenceData) (γ M : ℝ) (m : ℕ) :
    SFinite (referenceRadialWeightedCellMeasure D γ M m) := by
  unfold referenceRadialWeightedCellMeasure
  infer_instance

instance referenceRadialWeightedMeasure_sFinite (D : ReferenceData) (γ M : ℝ) :
    SFinite (referenceRadialWeightedMeasure D γ M) := by
  unfold referenceRadialWeightedMeasure
  infer_instance

instance referenceWeightedCellMeasure_sFinite (D : ReferenceData) (γ M : ℝ) (m : ℕ) :
    SFinite (referenceWeightedCellMeasure D γ M m) := by
  unfold referenceWeightedCellMeasure radialPhysicalMeasure
  infer_instance

instance referenceWeightedMeasure_sFinite (D : ReferenceData) (γ M : ℝ) :
    SFinite (referenceWeightedMeasure D γ M) := by
  unfold referenceWeightedMeasure
  infer_instance

theorem referenceRadialCellDensity_measurable {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) (m : ℕ) :
    Measurable (referenceRadialCellDensity D γ M m) :=
  (measurable_const.mul ((hD.1 m).continuous.measurable.pow_const 2)).ennreal_ofReal

theorem referenceCellMeasureDensity_eq_radial (D : ReferenceData) (γ M : ℝ) (m : ℕ) :
    referenceCellMeasureDensity D γ M m =
      ENNReal.ofReal ((2 * Real.pi)⁻¹) •
        (fun x : PolarPoint => referenceRadialCellDensity D γ M m x.1) := by
  funext x
  change ENNReal.ofReal (referenceCellMeasureWeight D γ M m * (D.localizer m x.1) ^ 2) =
    ENNReal.ofReal ((2 * Real.pi)⁻¹) *
      ENNReal.ofReal
        (Real.exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          (D.localizer m x.1) ^ 2)
  unfold referenceCellMeasureWeight
  rw [mul_assoc, ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]

theorem referenceWeightedCellMeasure_eq_prod {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) (m : ℕ) :
    referenceWeightedCellMeasure D γ M m =
      (referenceRadialWeightedCellMeasure D γ M m).prod referenceAngularMeasure := by
  unfold referenceWeightedCellMeasure referenceRadialWeightedCellMeasure referenceAngularMeasure
  rw [Measure.prod_smul_right, prod_withDensity_left (referenceRadialCellDensity_measurable hD γ M m),
    ← radialPhysicalMeasure_eq_prod, referenceCellMeasureDensity_eq_radial]
  simpa only [Function.comp_def] using
    withDensity_smul (μ := radialPhysicalMeasure D) (ENNReal.ofReal ((2 * Real.pi)⁻¹))
      ((referenceRadialCellDensity_measurable hD γ M m).comp measurable_fst)

theorem referenceWeightedMeasure_eq_prod {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) :
    referenceWeightedMeasure D γ M =
      (referenceRadialWeightedMeasure D γ M).prod referenceAngularMeasure := by
  unfold referenceWeightedMeasure referenceRadialWeightedMeasure
  rw [Measure.prod_sum_left]
  apply congrArg Measure.sum
  funext m
  exact referenceWeightedCellMeasure_eq_prod hD γ M m

end ContinuousFlexibility.Statements
