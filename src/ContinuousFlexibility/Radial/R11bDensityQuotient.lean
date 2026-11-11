import ContinuousFlexibility.Radial.R11bDensityL2

/-!
# Quotients and bounded densities in physical L²

Division by a positive density is transferred exactly to the inverse
square-root multiplier. Bounded nonnegative densities preserve L² membership.
-/

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped ENNReal

theorem r11b_memLp_div_withDensity_ofReal_iff
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w f : α → ℝ} (hw : AEMeasurable w μ) (hwpos : ∀ᵐ x ∂μ, 0 < w x) :
    MemLp (fun x => f x / w x) 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))) ↔
      MemLp (fun x => Real.sqrt ((w x)⁻¹) * f x) 2 μ := by
  rw [r11b_memLp_withDensity_ofReal_iff_of_pos hw hwpos]
  apply memLp_congr_ae
  exact Eventually.of_forall fun x => by
    calc
      Real.sqrt (w x) * (f x / w x) =
          (Real.sqrt (w x) / w x) * f x := by ring
      _ = Real.sqrt ((w x)⁻¹) * f x := by
        rw [Real.sqrt_div_self, Real.sqrt_inv]

theorem r11b_memLp_withDensity_ofReal_of_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w f : α → ℝ} {C : ℝ}
    (hw : AEMeasurable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hbound : ∀ᵐ x ∂μ, w x ≤ C) (hf : MemLp f 2 μ) :
    MemLp f 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))) := by
  apply (r11b_memLp_withDensity_ofReal_iff hw hw0 hf.aestronglyMeasurable).mpr
  apply hf.of_le_mul (c := Real.sqrt C)
    (hw.sqrt.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖Real.sqrt (w x) * f x‖ ≤ Real.sqrt C * ‖f x‖
  rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hx) (norm_nonneg _)

end ContinuousFlexibility.Radial
