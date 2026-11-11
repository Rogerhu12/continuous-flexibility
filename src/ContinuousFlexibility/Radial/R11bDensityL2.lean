import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# L² under a positive density and multiplication by its square root

These statements use the actual with-density measure and the original
representatives. With a positive density almost everywhere, no separate
measurability premise for the field is needed in the equivalence.
-/

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped ENNReal

theorem r11b_integral_sq_withDensity_ofReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w : α → ℝ} (hw : AEMeasurable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (f : α → ℝ) :
    (∫ x, f x ^ 2 ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) =
      ∫ x, (Real.sqrt (w x) * f x) ^ 2 ∂μ := by
  have htop : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ∞ :=
    Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul₀ hw.ennreal_ofReal htop]
  apply integral_congr_ae
  filter_upwards [hw0] with x hx
  rw [smul_eq_mul, ENNReal.toReal_ofReal hx, mul_pow, Real.sq_sqrt hx]

theorem r11b_memLp_withDensity_ofReal_iff
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w f : α → ℝ} (hw : AEMeasurable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))) ↔
      MemLp (fun x => Real.sqrt (w x) * f x) 2 μ := by
  have hfw : AEStronglyMeasurable f
      (μ.withDensity (fun x => ENNReal.ofReal (w x))) :=
    hf.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmul : AEStronglyMeasurable (fun x => Real.sqrt (w x) * f x) μ :=
    hw.sqrt.aestronglyMeasurable.mul hf
  have htop : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ∞ :=
    Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  rw [memLp_two_iff_integrable_sq hfw, memLp_two_iff_integrable_sq hmul,
    integrable_withDensity_iff_integrable_smul₀' hw.ennreal_ofReal htop]
  apply integrable_congr
  filter_upwards [hw0] with x hx
  rw [smul_eq_mul, ENNReal.toReal_ofReal hx, mul_pow, Real.sq_sqrt hx]

theorem r11b_memLp_withDensity_ofReal_iff_of_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w f : α → ℝ} (hw : AEMeasurable w μ) (hwpos : ∀ᵐ x ∂μ, 0 < w x) :
    MemLp f 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))) ↔
      MemLp (fun x => Real.sqrt (w x) * f x) 2 μ := by
  have hw0 : ∀ᵐ x ∂μ, 0 ≤ w x := hwpos.mono (fun x hx => hx.le)
  constructor
  · intro h
    have hne : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) ≠ 0 :=
      hwpos.mono (fun x hx => ne_of_gt (ENNReal.ofReal_pos.mpr hx))
    have hf : AEStronglyMeasurable f μ :=
      h.aestronglyMeasurable.mono_ac
        (withDensity_absolutelyContinuous' hw.ennreal_ofReal hne)
    exact (r11b_memLp_withDensity_ofReal_iff hw hw0 hf).mp h
  · intro h
    have hdiv : AEStronglyMeasurable
        (fun x => (Real.sqrt (w x) * f x) / Real.sqrt (w x)) μ :=
      (h.aestronglyMeasurable.aemeasurable.div hw.sqrt).aestronglyMeasurable
    have hf : AEStronglyMeasurable f μ := by
      apply hdiv.congr
      filter_upwards [hwpos] with x hx
      apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hx))).mpr
      ring
    exact (r11b_memLp_withDensity_ofReal_iff hw hw0 hf).mpr h

end ContinuousFlexibility.Radial
