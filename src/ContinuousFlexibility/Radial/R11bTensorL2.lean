module

public import ContinuousFlexibility.Radial.R11bModeL2

/-!
# Actual product L² tensors

Separate square-integrable radial and angular factors define an actual
product L² function. Its squared norm and cross inner product factor into
the corresponding ordinary integrals.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory

theorem r11b_norm_toLp_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, r11b_real_inner_toLp_eq_integral hf hf]
  simp only [pow_two]

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

theorem r11b_memLp_tensor {f : α → ℝ} {g : β → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2 (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : α × β => f z.1 * g z.2) (μ.prod ν) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [mul_pow] using hf.integrable_sq.mul_prod hg.integrable_sq

def r11bTensorL2 {f : α → ℝ} {g : β → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) : Lp ℝ 2 (μ.prod ν) :=
  (r11b_memLp_tensor hf hg).toLp (fun z => f z.1 * g z.2)

theorem r11bTensorL2_coeFn {f : α → ℝ} {g : β → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    (r11bTensorL2 hf hg : α × β → ℝ) =ᵐ[μ.prod ν]
      fun z => f z.1 * g z.2 :=
  (r11b_memLp_tensor hf hg).coeFn_toLp

theorem r11bTensorL2_norm_sq {f : α → ℝ} {g : β → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    ‖r11bTensorL2 hf hg‖ ^ 2 = (∫ x, f x ^ 2 ∂μ) * ∫ y, g y ^ 2 ∂ν := by
  unfold r11bTensorL2
  rw [r11b_norm_toLp_sq]
  simp_rw [mul_pow]
  exact integral_prod_mul (fun x => f x ^ 2) (fun y => g y ^ 2)

theorem r11bTensorL2_inner
    {f₁ f₂ : α → ℝ} {g₁ g₂ : β → ℝ}
    (hf₁ : MemLp f₁ 2 μ) (hf₂ : MemLp f₂ 2 μ)
    (hg₁ : MemLp g₁ 2 ν) (hg₂ : MemLp g₂ 2 ν) :
    inner ℝ (r11bTensorL2 hf₁ hg₁) (r11bTensorL2 hf₂ hg₂) =
      (∫ x, f₁ x * f₂ x ∂μ) * ∫ y, g₁ y * g₂ y ∂ν := by
  unfold r11bTensorL2
  rw [r11b_real_inner_toLp_eq_integral]
  calc
    (∫ z : α × β, (f₁ z.1 * g₁ z.2) * (f₂ z.1 * g₂ z.2) ∂μ.prod ν) =
        ∫ z : α × β, (f₁ z.1 * f₂ z.1) * (g₁ z.2 * g₂ z.2) ∂μ.prod ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)
    _ = (∫ x, f₁ x * f₂ x ∂μ) * ∫ y, g₁ y * g₂ y ∂ν :=
      integral_prod_mul (fun x => f₁ x * f₂ x) (fun y => g₁ y * g₂ y)

end ContinuousFlexibility.Radial
