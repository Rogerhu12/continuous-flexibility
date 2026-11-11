import ContinuousFlexibility.Analysis.N01aReferenceCellSquares
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The physical measure and the actual reference cell integrals
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal

theorem radialPhysicalMeasure_eq_prod_Ioc (D : ReferenceData) :
    radialPhysicalMeasure D =
      (volume.restrict (Ioc D.a D.b)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  rw [radialPhysicalMeasure_eq_prod, radialCore, restrict_Ioo_eq_restrict_Ioc]

instance radialPhysicalMeasure_isFiniteMeasure (D : ReferenceData) :
    IsFiniteMeasure (radialPhysicalMeasure D) := by
  rw [radialPhysicalMeasure_eq_prod_Ioc]
  infer_instance

theorem radialPhysicalMeasure_ae_radialCore (D : ReferenceData) :
    ∀ᵐ p ∂radialPhysicalMeasure D, p.1 ∈ radialCore D := by
  exact (ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)).mono
    fun _ hp => hp.1

theorem RadialCellIntegrable.integrable_square {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (m : ℕ) :
    Integrable (fun p => (D.localizer m p.1 * f p) ^ 2) (radialPhysicalMeasure D) :=
  (hf m).integrable_sq

/-- The normalization in `referenceCellSquare` is exactly the normalized
angular integral of its square over the physical annulus. -/
theorem n01a_referenceCellSquare_eq_integral {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (m : ℕ) :
    referenceCellSquare D m f = (2 * Real.pi)⁻¹ *
      ∫ p, (D.localizer m p.1 * f p) ^ 2 ∂radialPhysicalMeasure D := by
  exact referenceCellSquare_eq_integral hab m hf

theorem integral_reference_cell_square {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (m : ℕ) :
    (∫ p, (D.localizer m p.1 * f p) ^ 2 ∂radialPhysicalMeasure D) =
      (2 * Real.pi) * referenceCellSquare D m f := by
  rw [n01a_referenceCellSquare_eq_integral hab hf m]
  field_simp [Real.pi_ne_zero]

end ContinuousFlexibility.Statements
