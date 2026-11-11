import ContinuousFlexibility.Analysis.IntervalLayerCutoff
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform derivative bounds for endpoint-layer cutoffs

The fixed smooth transition has compactly supported derivative. Scaling
therefore gives a single bound `A / δ` for every interval and every outer
layer width `Δ ≥ δ > 0`.
-/

open Set Filter
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem hasCompactSupport_deriv_smoothTransition :
    HasCompactSupport (deriv Real.smoothTransition) := by
  have hs : Function.support (deriv Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    change deriv Real.smoothTransition x ≠ 0 at hx
    by_contra hn
    have hcases : x < 0 ∨ 1 < x := by
      by_cases h₀ : 0 ≤ x
      · exact Or.inr (lt_of_not_ge fun h₁ => hn ⟨h₀, h₁⟩)
      · exact Or.inl (lt_of_not_ge h₀)
    rcases hcases with hl | hr
    · have hd : HasDerivAt Real.smoothTransition 0 x :=
        (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (by
          filter_upwards [gt_mem_nhds hl] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le)
      exact hx hd.deriv
    · have hd : HasDerivAt Real.smoothTransition 0 x :=
        (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq (by
          filter_upwards [lt_mem_nhds hr] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le)
      exact hx hd.deriv
  exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (closure_minimal hs isClosed_Icc)

private theorem layer_deriv_mul_le {f g : ℝ → ℝ} {x A B : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hf₀ : |f x| ≤ 1) (hg₀ : |g x| ≤ 1)
    (hf₁ : |deriv f x| ≤ A) (hg₁ : |deriv g x| ≤ B) :
    |deriv (fun y => f y * g y) x| ≤ A + B := by
  rw [deriv_fun_mul hf hg]
  calc
    |deriv f x * g x + f x * deriv g x| ≤
        |deriv f x * g x| + |f x * deriv g x| := abs_add_le _ _
    _ ≤ A + B := by
      rw [abs_mul, abs_mul]
      have h₁ := (mul_le_mul_of_nonneg_left hg₀ (abs_nonneg (deriv f x))).trans
        (by simpa only [mul_one] using hf₁)
      have h₂ := (mul_le_mul_of_nonneg_right hf₀ (abs_nonneg (deriv g x))).trans
        (by simpa only [one_mul] using hg₁)
      exact add_le_add h₁ h₂

private theorem layer_threshold_deriv_le {g : ℝ → ℝ} {x δ B : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B)
    (hbound : ∀ y, |deriv Real.smoothTransition y| ≤ B)
    (hg : DifferentiableAt ℝ g x) (hgd : |deriv g x| ≤ 1) :
    |deriv (fun y => intervalLayerThreshold δ (g y)) x| ≤ B / δ := by
  have hS : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable (by simp)
  have harg := (hg.hasDerivAt.div_const δ).sub_const 1
  have hd := ((hS (g x / δ - 1)).hasDerivAt.comp x harg).deriv
  change |deriv (fun y => Real.smoothTransition (g y / δ - 1)) x| ≤ _
  rw [hd, abs_mul, abs_div, abs_of_pos hδ]
  calc
    |deriv Real.smoothTransition (g x / δ - 1)| * (|deriv g x| / δ) ≤
        B * (1 / δ) :=
      mul_le_mul (hbound _) (div_le_div_of_nonneg_right hgd hδ.le)
        (div_nonneg (abs_nonneg _) hδ.le) hB
    _ = B / δ := by ring

private theorem layer_threshold_abs_le (δ x : ℝ) :
    |intervalLayerThreshold δ x| ≤ 1 := by
  rw [abs_of_nonneg (intervalLayerThreshold_bounds δ x).1]
  exact (intervalLayerThreshold_bounds δ x).2

theorem intervalLayerCutoff_deriv_le {B a b δ Δ x : ℝ}
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) (hB : 0 ≤ B)
    (hbound : ∀ y, |deriv Real.smoothTransition y| ≤ B) :
    |deriv (intervalLayerCutoff a b δ Δ) x| ≤ 6 * B / δ := by
  have hΔ : 0 < Δ := hδ.trans_le hδΔ
  have hδh : 0 < δ / 2 := by positivity
  let f : ℝ → ℝ := fun y => intervalLayerThreshold (δ / 2) (y - a)
  let g : ℝ → ℝ := fun y => intervalLayerThreshold (δ / 2) (b - y)
  let h : ℝ → ℝ := fun y => intervalLayerThreshold Δ (y - a)
  let k : ℝ → ℝ := fun y => intervalLayerThreshold Δ (b - y)
  have hf : ContDiff ℝ ∞ f := (contDiff_intervalLayerThreshold (δ / 2)).comp
    (contDiff_id.sub contDiff_const)
  have hg : ContDiff ℝ ∞ g := (contDiff_intervalLayerThreshold (δ / 2)).comp
    (contDiff_const.sub contDiff_id)
  have hh : ContDiff ℝ ∞ h := (contDiff_intervalLayerThreshold Δ).comp
    (contDiff_id.sub contDiff_const)
  have hk : ContDiff ℝ ∞ k := (contDiff_intervalLayerThreshold Δ).comp
    (contDiff_const.sub contDiff_id)
  have hleft : |deriv (fun y : ℝ => y - a) x| ≤ 1 := by
    rw [((hasDerivAt_id x).sub_const a).deriv]
    norm_num
  have hright : |deriv (fun y : ℝ => b - y) x| ≤ 1 := by
    rw [((hasDerivAt_id x).const_sub b).deriv]
    norm_num
  have hf₁ : |deriv f x| ≤ B / (δ / 2) :=
    layer_threshold_deriv_le hδh hB hbound
      ((hasDerivAt_id x).sub_const a).differentiableAt hleft
  have hg₁ : |deriv g x| ≤ B / (δ / 2) :=
    layer_threshold_deriv_le hδh hB hbound
      ((hasDerivAt_id x).const_sub b).differentiableAt hright
  have hh₁ : |deriv h x| ≤ B / Δ :=
    layer_threshold_deriv_le hΔ hB hbound
      ((hasDerivAt_id x).sub_const a).differentiableAt hleft
  have hk₁ : |deriv k x| ≤ B / Δ :=
    layer_threshold_deriv_le hΔ hB hbound
      ((hasDerivAt_id x).const_sub b).differentiableAt hright
  have hfg₁ : |deriv (fun y => f y * g y) x| ≤ B / (δ / 2) + B / (δ / 2) :=
    layer_deriv_mul_le (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)
      (layer_threshold_abs_le _ _) (layer_threshold_abs_le _ _) hf₁ hg₁
  have hhk₁ : |deriv (fun y => h y * k y) x| ≤ B / Δ + B / Δ :=
    layer_deriv_mul_le (hh.differentiable (by simp) x) (hk.differentiable (by simp) x)
      (layer_threshold_abs_le _ _) (layer_threshold_abs_le _ _) hh₁ hk₁
  have hfg₀ : |f x * g x| ≤ 1 := by
    rw [abs_mul]
    have ht := mul_le_mul (layer_threshold_abs_le (δ / 2) (x - a))
      (layer_threshold_abs_le (δ / 2) (b - x)) (abs_nonneg (g x)) zero_le_one
    simpa only [one_mul] using ht
  have hhk₀ : 0 ≤ h x * k x ∧ h x * k x ≤ 1 := by
    have h₀ := (intervalLayerThreshold_bounds Δ (x - a)).1
    have k₀ := (intervalLayerThreshold_bounds Δ (b - x)).1
    refine ⟨mul_nonneg h₀ k₀, ?_⟩
    exact (mul_le_mul_of_nonneg_left (intervalLayerThreshold_bounds Δ (b - x)).2 h₀).trans
      (by simpa only [mul_one] using (intervalLayerThreshold_bounds Δ (x - a)).2)
  have houter₀ : |1 - h x * k x| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hhk₀.2)]
    linarith [hhk₀.1]
  have hprod : DifferentiableAt ℝ (fun y => h y * k y) x :=
    (hh.differentiable (by simp) x).mul (hk.differentiable (by simp) x)
  have houter₁ : |deriv (fun y => 1 - h y * k y) x| ≤ B / Δ + B / Δ := by
    rw [(hprod.hasDerivAt.const_sub 1).deriv, abs_neg]
    exact hhk₁
  have hinner : DifferentiableAt ℝ (fun y => f y * g y) x :=
    (hf.differentiable (by simp) x).mul (hg.differentiable (by simp) x)
  have hfinal := layer_deriv_mul_le hinner (hprod.const_sub 1) hfg₀ houter₀ hfg₁ houter₁
  have hdiv : B / Δ ≤ B / δ := div_le_div_of_nonneg_left hB hδ hδΔ
  change |deriv (fun y => (f y * g y) * (1 - h y * k y)) x| ≤ _
  calc
    _ ≤ (B / (δ / 2) + B / (δ / 2)) + (B / Δ + B / Δ) := hfinal
    _ ≤ (B / (δ / 2) + B / (δ / 2)) + (B / δ + B / δ) :=
      add_le_add_left (add_le_add hdiv hdiv) _
    _ = 6 * B / δ := by ring

/-- A single derivative constant works for every interval and every layer. -/
theorem exists_intervalLayerCutoff_deriv_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ a b δ Δ x : ℝ, 0 < δ → δ ≤ Δ →
      |deriv (intervalLayerCutoff a b δ Δ) x| ≤ A / δ := by
  have hS : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp hS).2.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hasCompactSupport_deriv_smoothTransition
  have hB₀ : 0 ≤ B := (norm_nonneg (deriv Real.smoothTransition 0)).trans (hB 0)
  refine ⟨6 * (B + 1), by positivity, ?_⟩
  intro a b δ Δ x hδ hδΔ
  have hb : ∀ y, |deriv Real.smoothTransition y| ≤ B := by
    intro y
    simpa only [Real.norm_eq_abs] using hB y
  exact (intervalLayerCutoff_deriv_le hδ hδΔ hB₀ hb).trans
    (div_le_div_of_nonneg_right (by linarith : 6 * B ≤ 6 * (B + 1)) hδ.le)

end

end ContinuousFlexibility.Analysis
