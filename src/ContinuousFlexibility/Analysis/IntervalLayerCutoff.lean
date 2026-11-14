module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Smooth cutoffs for two endpoint layers

A single formula treats both ends of an interval. The cutoff is one where
the distance to the endpoints lies in `[δ, Δ]`, and its topological support
lies in the enlarged layer `[δ / 2, 2 * Δ]`. It is independent of any given
partition of unity and therefore requires no derivatives of that partition.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace ContinuousFlexibility.Analysis

noncomputable section

set_option backward.isDefEq.respectTransparency false

def intervalEndpointDistance (a b x : ℝ) : ℝ := min (x - a) (b - x)

def intervalLayerThreshold (δ x : ℝ) : ℝ :=
  Real.smoothTransition (x / δ - 1)

def intervalLayerCutoff (a b δ Δ x : ℝ) : ℝ :=
  intervalLayerThreshold (δ / 2) (x - a) *
    intervalLayerThreshold (δ / 2) (b - x) *
      (1 - intervalLayerThreshold Δ (x - a) * intervalLayerThreshold Δ (b - x))

def intervalEndpointLayer (a b δ Δ : ℝ) : Set ℝ :=
  {x | δ / 2 ≤ intervalEndpointDistance a b x ∧
    intervalEndpointDistance a b x ≤ 2 * Δ}

theorem continuous_intervalEndpointDistance (a b : ℝ) :
    Continuous (intervalEndpointDistance a b) :=
  (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)

theorem isClosed_intervalEndpointLayer (a b δ Δ : ℝ) :
    IsClosed (intervalEndpointLayer a b δ Δ) :=
  isClosed_Icc.preimage (continuous_intervalEndpointDistance a b)

theorem contDiff_intervalLayerThreshold (δ : ℝ) :
    ContDiff ℝ ∞ (intervalLayerThreshold δ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.div_const δ).sub contDiff_const)

theorem intervalLayerThreshold_bounds (δ x : ℝ) :
    0 ≤ intervalLayerThreshold δ x ∧ intervalLayerThreshold δ x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem intervalLayerThreshold_zero {δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ δ) :
    intervalLayerThreshold δ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : x / δ ≤ 1 := (div_le_iff₀ hδ).2 (by simpa only [one_mul] using hx)
  linarith

theorem intervalLayerThreshold_one {δ x : ℝ} (hδ : 0 < δ) (hx : 2 * δ ≤ x) :
    intervalLayerThreshold δ x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : (2 : ℝ) ≤ x / δ := (le_div_iff₀ hδ).2 hx
  linarith

theorem contDiff_intervalLayerCutoff (a b δ Δ : ℝ) :
    ContDiff ℝ ∞ (intervalLayerCutoff a b δ Δ) := by
  exact (((contDiff_intervalLayerThreshold (δ / 2)).comp
    (contDiff_id.sub contDiff_const)).mul
    ((contDiff_intervalLayerThreshold (δ / 2)).comp
      (contDiff_const.sub contDiff_id))).mul
    (contDiff_const.sub (((contDiff_intervalLayerThreshold Δ).comp
      (contDiff_id.sub contDiff_const)).mul
      ((contDiff_intervalLayerThreshold Δ).comp (contDiff_const.sub contDiff_id))))

private theorem layer_mul_bounds {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) : 0 ≤ x * y ∧ x * y ≤ 1 :=
  ⟨mul_nonneg hx.1 hy.1,
    (mul_le_mul_of_nonneg_left hy.2 hx.1).trans (by simpa only [mul_one] using hx.2)⟩

theorem intervalLayerCutoff_bounds (a b δ Δ x : ℝ) :
    0 ≤ intervalLayerCutoff a b δ Δ x ∧ intervalLayerCutoff a b δ Δ x ≤ 1 := by
  have hi := layer_mul_bounds (intervalLayerThreshold_bounds (δ / 2) (x - a))
    (intervalLayerThreshold_bounds (δ / 2) (b - x))
  have ho := layer_mul_bounds (intervalLayerThreshold_bounds Δ (x - a))
    (intervalLayerThreshold_bounds Δ (b - x))
  exact layer_mul_bounds hi ⟨by linarith, by linarith⟩

theorem intervalLayerCutoff_one {a b δ Δ x : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hlo : δ ≤ intervalEndpointDistance a b x)
    (hhi : intervalEndpointDistance a b x ≤ Δ) :
    intervalLayerCutoff a b δ Δ x = 1 := by
  have hδh : 0 < δ / 2 := by positivity
  have hx := le_min_iff.mp hlo
  have hl : intervalLayerThreshold (δ / 2) (x - a) = 1 :=
    intervalLayerThreshold_one hδh (by linarith [hx.1])
  have hr : intervalLayerThreshold (δ / 2) (b - x) = 1 :=
    intervalLayerThreshold_one hδh (by linarith [hx.2])
  have ho : intervalLayerThreshold Δ (x - a) * intervalLayerThreshold Δ (b - x) = 0 := by
    rcases le_total (x - a) (b - x) with h | h
    · have hh : x - a ≤ Δ := by simpa only [intervalEndpointDistance, min_eq_left h] using hhi
      rw [intervalLayerThreshold_zero hΔ hh, zero_mul]
    · have hh : b - x ≤ Δ := by simpa only [intervalEndpointDistance, min_eq_right h] using hhi
      rw [intervalLayerThreshold_zero hΔ hh, mul_zero]
  simp only [intervalLayerCutoff, hl, hr, ho, sub_zero, mul_one]

theorem tsupport_intervalLayerCutoff_subset {a b δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    tsupport (intervalLayerCutoff a b δ Δ) ⊆ intervalEndpointLayer a b δ Δ := by
  apply closure_minimal _ (isClosed_intervalEndpointLayer a b δ Δ)
  intro x hx
  change intervalLayerCutoff a b δ Δ x ≠ 0 at hx
  have hprod := mul_ne_zero_iff.mp hx
  have hin := mul_ne_zero_iff.mp hprod.1
  have hδh : 0 < δ / 2 := by positivity
  have hl : δ / 2 < x - a := lt_of_not_ge fun h =>
    hin.1 (intervalLayerThreshold_zero hδh h)
  have hr : δ / 2 < b - x := lt_of_not_ge fun h =>
    hin.2 (intervalLayerThreshold_zero hδh h)
  refine ⟨le_min hl.le hr.le, ?_⟩
  by_contra hh
  have hmin : 2 * Δ < min (x - a) (b - x) := lt_of_not_ge hh
  have hb := lt_min_iff.mp hmin
  apply hprod.2
  rw [intervalLayerThreshold_one hΔ hb.1.le,
    intervalLayerThreshold_one hΔ hb.2.le]
  norm_num

theorem intervalEndpointLayer_subset_Ioo {a b δ Δ : ℝ} (hδ : 0 < δ) :
    intervalEndpointLayer a b δ Δ ⊆ Ioo a b := by
  intro x hx
  have hh : 0 < min (x - a) (b - x) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < δ / 2) hx.1
  have hb := lt_min_iff.mp hh
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

theorem hasCompactSupport_intervalLayerCutoff {a b δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    HasCompactSupport (intervalLayerCutoff a b δ Δ) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    ((tsupport_intervalLayerCutoff_subset hδ hΔ).trans
      ((intervalEndpointLayer_subset_Ioo hδ).trans Ioo_subset_Icc_self))

end

end ContinuousFlexibility.Analysis
