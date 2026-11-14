module

public import ContinuousFlexibility.Radial.R11bTensorL2

/-!
# Bounded multiplication preserves strong L² limits

All functions below are actual measurable representatives. The norm estimate
is proved on their Lp classes from the pointwise multiplication bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem r11b_memLp_mul_bounded {a f : α → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)
    (hf : MemLp f 2 μ) :
    MemLp (fun x => a x * f x) 2 μ := by
  apply hf.of_le_mul (ha.mul hf.aestronglyMeasurable)
  filter_upwards [hC] with x hx
  change ‖a x * f x‖ ≤ C * ‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem r11b_toLp_mul_sub_norm_le {a f g : α → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖(r11b_memLp_mul_bounded ha hC hf).toLp (fun x => a x * f x) -
      (r11b_memLp_mul_bounded ha hC hg).toLp (fun x => a x * g x)‖ ≤
        C * ‖hf.toLp f - hg.toLp g‖ := by
  let F : Lp ℝ 2 μ := (r11b_memLp_mul_bounded ha hC hf).toLp (fun x => a x * f x)
  let G : Lp ℝ 2 μ := (r11b_memLp_mul_bounded ha hC hg).toLp (fun x => a x * g x)
  change ‖F - G‖ ≤ C * ‖hf.toLp f - hg.toLp g‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub F G, Lp.coeFn_sub (hf.toLp f) (hg.toLp g),
    (r11b_memLp_mul_bounded ha hC hf).coeFn_toLp,
    (r11b_memLp_mul_bounded ha hC hg).coeFn_toLp,
    hf.coeFn_toLp, hg.coeFn_toLp, hC] with x hsub hsub' hF hG hfx hgx hax
  change F x = a x * f x at hF
  change G x = a x * g x at hG
  simp only [Pi.sub_apply] at hsub hsub'
  rw [hsub, hsub', hF, hG, hfx, hgx, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right hax (norm_nonneg _)

theorem r11b_tendsto_toLp_mul_bounded
    {ι : Type*} {l : Filter ι} {a : α → ℝ} {C : ℝ}
    {f : ι → α → ℝ} {g : α → ℝ}
    (ha : AEStronglyMeasurable a μ) (hC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g))) :
    Tendsto (fun i => (r11b_memLp_mul_bounded ha hC (hf i)).toLp
      (fun x => a x * f i x)) l
      (𝓝 ((r11b_memLp_mul_bounded ha hC hg).toLp (fun x => a x * g x))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hlim ⊢
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => r11b_toLp_mul_sub_norm_le ha hC (hf i) hg)
  simpa only [mul_zero] using hlim.const_mul C

end ContinuousFlexibility.Radial
