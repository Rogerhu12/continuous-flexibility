import ContinuousFlexibility.Radial.R11bLocalL2
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Physical integrals and the normalized radial cell squares

The graph uses iterated interval integrals, whereas local L² membership uses
the product physical measure.  Fubini's theorem identifies them only after
actual integrability has been established.  These lemmas retain that premise
and the paper's angular normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements

theorem r11b_radialPhysicalMeasure_eq_prod (D : ReferenceData) :
    radialPhysicalMeasure D =
      ((volume : Measure ℝ).restrict (radialCore D)).prod
        ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
    (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) = _
  rw [← Measure.prod_restrict]

/-- The angular mean contributes exactly the factor (2π)⁻¹. -/
theorem r11b_integral_angularMean_eq {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : Integrable f (radialPhysicalMeasure D)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
      (2 * Real.pi)⁻¹ * ∫ x, f x ∂radialPhysicalMeasure D := by
  have hp : Integrable f (((volume : Measure ℝ).restrict (radialCore D)).prod
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rwa [r11b_radialPhysicalMeasure_eq_prod] at hf
  have hrad : (volume : Measure ℝ).restrict (radialCore D) =
      (volume : Measure ℝ).restrict (Ioc D.a D.b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  unfold radialAngularMean
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
  rw [← hrad, r11b_radialPhysicalMeasure_eq_prod, integral_prod _ hp]

/-- The old iterated square norm equals the actual localized physical L² integral. -/
theorem r11b_referenceCellSquare_eq_integral {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (m : ℕ) :
    referenceCellSquare D m f =
      (2 * Real.pi)⁻¹ * ∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D :=
  r11b_integral_angularMean_eq hab (hf m).integrable_sq

/-- Equality of physical representatives preserves an integrable mean pairing. -/
theorem r11b_integral_angularMean_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ} (hf : Integrable f (radialPhysicalMeasure D))
    (hg : Integrable g (radialPhysicalMeasure D))
    (hfg : f =ᵐ[radialPhysicalMeasure D] g) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ)) := by
  rw [r11b_integral_angularMean_eq hab hf, r11b_integral_angularMean_eq hab hg,
    integral_congr_ae hfg]

end ContinuousFlexibility.Radial
