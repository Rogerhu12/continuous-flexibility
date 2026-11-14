module

public import ContinuousFlexibility.Radial.ReferenceCosineProjection
public import ContinuousFlexibility.Radial.ReferenceFourierL2

/-!
# Radial L² bounds for actual angular coefficients

Normalized angular coefficients are contractions on each radial fiber.
Fubini transfers that estimate to arbitrary radial product measures and
then to each frozen localized cell.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

/-- The scalar radial coefficient of the mean/even-cosine basis. -/
def referenceRadialCoefficient (u : PolarPoint → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  referenceAngularCoefficient (fun θ => u (r, θ)) n

@[simp] theorem referenceRadialCoefficient_zero (u : PolarPoint → ℝ) (r : ℝ) :
    referenceRadialCoefficient u 0 r = radialAngularMean (fun θ => u (r, θ)) := by
  simp only [referenceRadialCoefficient, referenceAngularCoefficient_zero]

@[simp] theorem referenceRadialCoefficient_succ (u : PolarPoint → ℝ) (n : ℕ) (r : ℝ) :
    referenceRadialCoefficient u (n + 1) r = referenceMode u (2 * (n + 1)) r := rfl

theorem referenceRadialCoefficient_mul_radial (a : ℝ → ℝ) (u : PolarPoint → ℝ) (n : ℕ) :
    referenceRadialCoefficient (fun x => a x.1 * u x) n =
      (fun r => a r * referenceRadialCoefficient u n r) := by
  funext r
  exact referenceAngularCoefficient_const_mul (a r) (fun θ => u (r, θ)) n

theorem aestronglyMeasurable_referenceRadialCoefficient {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) (n : ℕ) :
    AEStronglyMeasurable (referenceRadialCoefficient u n) μ := by
  have hm : AEStronglyMeasurable
      (fun x : PolarPoint => u x * referenceAngularBasis n x.2)
      (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :=
    hu.mul (((contDiff_referenceAngularBasis n).continuous.comp continuous_snd).aestronglyMeasurable)
  have hi := hm.integral_prod_right'
  have hscaled := hi.const_mul ((2 * Real.pi)⁻¹)
  change AEStronglyMeasurable (fun r => (2 * Real.pi)⁻¹ *
    ∫ θ in (0 : ℝ)..2 * Real.pi, u (r, θ) * referenceAngularBasis n θ) μ
  simpa only [intervalIntegral.integral_of_le
    (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] using hscaled

theorem integrable_radialAngularMean_sq {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) :
    Integrable (fun r => radialAngularMean (fun θ => u (r, θ) ^ 2)) μ := by
  have hi := hu.integrable_sq.integral_prod_left.const_mul ((2 * Real.pi)⁻¹)
  simpa only [radialAngularMean,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] using hi

theorem memLp_referenceRadialCoefficient_prod {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) (n : ℕ) :
    MemLp (referenceRadialCoefficient u n) 2 μ := by
  have hm := aestronglyMeasurable_referenceRadialCoefficient hu.aestronglyMeasurable n
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrable_radialAngularMean_sq hu).mono' (hm.pow 2)
  filter_upwards [memLp_two_prod_sections hu] with r hr
  change ‖referenceRadialCoefficient u n r ^ 2‖ ≤
    radialAngularMean (fun θ => u (r, θ) ^ 2)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact referenceAngularCoefficient_sq_le hr n

theorem integral_referenceRadialCoefficient_sq_le_prod {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) (n : ℕ) :
    (∫ r, referenceRadialCoefficient u n r ^ 2 ∂μ) ≤
      (2 * Real.pi)⁻¹ *
        ∫ x, u x ^ 2 ∂μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  calc
    (∫ r, referenceRadialCoefficient u n r ^ 2 ∂μ) ≤
        ∫ r, radialAngularMean (fun θ => u (r, θ) ^ 2) ∂μ := by
      apply integral_mono_ae (memLp_referenceRadialCoefficient_prod hu n).integrable_sq
        (integrable_radialAngularMean_sq hu)
      filter_upwards [memLp_two_prod_sections hu] with r hr
      exact referenceAngularCoefficient_sq_le hr n
    _ = _ := by
      simp only [radialAngularMean,
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
      rw [integral_const_mul, ← integral_prod _ hu.integrable_sq]

theorem referenceRadialCoefficient_memLp_cell {D : ReferenceData} {u : PolarPoint → ℝ}
    (hu : RadialCellIntegrable D u) (n m : ℕ) :
    MemLp (fun r => D.localizer m r * referenceRadialCoefficient u n r) 2
      (volume.restrict (radialCore D)) := by
  have hm : MemLp (fun x : PolarPoint => D.localizer m x.1 * u x) 2
      ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hu m
  simpa only [referenceRadialCoefficient_mul_radial] using
    memLp_referenceRadialCoefficient_prod hm n

/-- Each scalar localized coefficient square is bounded by the frozen
physical cell square, with no normalization loss. -/
theorem referenceRadialCoefficient_cell_sq_le {D : ReferenceData} (hab : D.a ≤ D.b)
    {u : PolarPoint → ℝ} (hu : RadialCellIntegrable D u) (n m : ℕ) :
    (∫ r, (D.localizer m r * referenceRadialCoefficient u n r) ^ 2
      ∂volume.restrict (radialCore D)) ≤ referenceCellSquare D m u := by
  have hm : MemLp (fun x : PolarPoint => D.localizer m x.1 * u x) 2
      ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hu m
  rw [referenceCellSquare_eq_integral hab m hu, radialPhysicalMeasure_eq_prod]
  simpa only [referenceRadialCoefficient_mul_radial] using
    integral_referenceRadialCoefficient_sq_le_prod hm n

end

end ContinuousFlexibility.Radial
