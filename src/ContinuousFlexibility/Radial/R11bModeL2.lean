module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Single-mode L² estimates for an actual product measure

A square-integrable angular factor defines a bounded coefficient map on a
product L² space. The coefficient is the original integral of representatives.
The proof uses Cauchy–Schwarz on almost every section, followed by Fubini.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped ENNReal

theorem r11b_real_inner_toLp_eq_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hxf hxg
  rw [Real.inner_apply, hxf, hxg]

theorem r11b_integral_mul_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [r11b_real_inner_toLp_eq_integral hf hg,
    r11b_real_inner_toLp_eq_integral hf hf,
    r11b_real_inner_toLp_eq_integral hg hg] at h
  simpa only [pow_two] using h

theorem r11b_memLp_modeCoefficient
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} {e : β → ℝ}
    (hf : MemLp f 2 (μ.prod ν)) (he : MemLp e 2 ν) :
    MemLp (fun x => ∫ y, f (x, y) * e y ∂ν) 2 μ ∧
      (∫ x, (∫ y, f (x, y) * e y ∂ν) ^ 2 ∂μ) ≤
        (∫ y, e y ^ 2 ∂ν) * ∫ z, f z ^ 2 ∂μ.prod ν := by
  have hmeas : AEStronglyMeasurable
      (fun x => ∫ y, f (x, y) * e y ∂ν) μ :=
    (hf.aestronglyMeasurable.mul he.aestronglyMeasurable.comp_snd).integral_prod_right'
  have hsections : ∀ᵐ x ∂μ, MemLp (fun y => f (x, y)) 2 ν := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.integrable_sq.prod_right_ae]
      with x hm hi
    exact (memLp_two_iff_integrable_sq hm).mpr hi
  have hpoint : ∀ᵐ x ∂μ,
      (∫ y, f (x, y) * e y ∂ν) ^ 2 ≤
        (∫ y, e y ^ 2 ∂ν) * ∫ y, f (x, y) ^ 2 ∂ν := by
    filter_upwards [hsections] with x hx
    exact (r11b_integral_mul_sq_le hx he).trans_eq (mul_comm _ _)
  have hmajor : Integrable
      (fun x => (∫ y, e y ^ 2 ∂ν) * ∫ y, f (x, y) ^ 2 ∂ν) μ :=
    hf.integrable_sq.integral_prod_left.const_mul _
  have hsq : Integrable (fun x => (∫ y, f (x, y) * e y ∂ν) ^ 2) μ := by
    apply hmajor.mono' (hmeas.pow 2)
    filter_upwards [hpoint] with x hx
    change ‖(∫ y, f (x, y) * e y ∂ν) ^ 2‖ ≤
      (∫ y, e y ^ 2 ∂ν) * ∫ y, f (x, y) ^ 2 ∂ν
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  refine ⟨(memLp_two_iff_integrable_sq hmeas).mpr hsq, ?_⟩
  calc
    (∫ x, (∫ y, f (x, y) * e y ∂ν) ^ 2 ∂μ) ≤
        ∫ x, (∫ y, e y ^ 2 ∂ν) * ∫ y, f (x, y) ^ 2 ∂ν ∂μ :=
      integral_mono_ae hsq hmajor hpoint
    _ = (∫ y, e y ^ 2 ∂ν) * ∫ z, f z ^ 2 ∂μ.prod ν := by
      rw [integral_const_mul, ← integral_prod _ hf.integrable_sq]

theorem r11b_modeCoefficient_contraction
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} {e : β → ℝ}
    (hf : MemLp f 2 (μ.prod ν)) (he : MemLp e 2 ν)
    (he_unit : (∫ y, e y ^ 2 ∂ν) = 1) :
    MemLp (fun x => ∫ y, f (x, y) * e y ∂ν) 2 μ ∧
      (∫ x, (∫ y, f (x, y) * e y ∂ν) ^ 2 ∂μ) ≤ ∫ z, f z ^ 2 ∂μ.prod ν := by
  simpa only [he_unit, one_mul] using r11b_memLp_modeCoefficient hf he

end ContinuousFlexibility.Radial
