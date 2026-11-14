import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.Linarith

/-!
# Quantitative normalization buffers on the actual positive components

Compact normalization support has one positive distance from the ends of
every component it meets. Four points at one fixed fraction of each component
span therefore give the existing buffer record with uniform lower bounds on
all five consecutive gaps. Ambient endpoints are included.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

/-- The support margin is fixed before the component. No separation from
the ambient endpoints is imposed on the components themselves. -/
theorem n04PositiveNormalizationSupport_uniform_distance
    {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {K : Set ℝ} (hK : IsCompact K) (hKP : K ⊆ n04PositiveRegion a b f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i : N04PositiveComponent a b f,
      ∀ x ∈ K ∩ i.val,
        n04PositiveLeft i + δ < x ∧ x + δ < n04PositiveRight i := by
  obtain ⟨ρ, hρ, hthick⟩ :=
    hK.exists_thickening_subset_open (n04PositiveRegion_isOpen hf) hKP
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  intro i x hx
  have hI : Ioo (x - ρ) (x + ρ) ⊆ n04PositiveRegion a b f := by
    intro y hy
    apply hthick
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, hx.1, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hxI : x ∈ Ioo (x - ρ) (x + ρ) := by
    constructor <;> linarith
  have hIi : Ioo (x - ρ) (x + ρ) ⊆ i.val := by
    rw [n04PositiveComponent_eq_component i hx.2]
    exact isPreconnected_Ioo.subset_connectedComponentIn hxI hI
  have hinside (y : ℝ) (hy : y ∈ Ioo (x - ρ) (x + ρ)) :
      n04PositiveLeft i < y ∧ y < n04PositiveRight i :=
    (n04PositiveComponent_mem_iff hf i).mp (hIi hy)
  have hleft := hinside (x - ρ / 2) (by constructor <;> linarith)
  have hright := hinside (x + ρ / 2) (by constructor <;> linarith)
  constructor <;> linarith [hleft.1, hright.2]

/-- Choose the existing normalization-buffer representation with one
positive proportional lower bound on every consecutive gap. This choice
precedes all states and preserves the original compact support. -/
theorem n04PositiveNormalizationBuffer_exists_uniform_margins
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : Continuous f)
    {K : Set ℝ} (hK : IsCompact K) (hKP : K ⊆ n04PositiveRegion a b f) :
    ∃ B : N04PositiveNormalizationBuffer a b f K, ∃ c : ℝ, 0 < c ∧
      ∀ i : N04PositiveComponent a b f,
        c * (n04PositiveRight i - n04PositiveLeft i) ≤
          B.centerLeft i - n04PositiveLeft i ∧
        c * (n04PositiveRight i - n04PositiveLeft i) ≤
          B.normalizationLeft i - B.centerLeft i ∧
        c * (n04PositiveRight i - n04PositiveLeft i) ≤
          B.normalizationRight i - B.normalizationLeft i ∧
        c * (n04PositiveRight i - n04PositiveLeft i) ≤
          B.centerRight i - B.normalizationRight i ∧
        c * (n04PositiveRight i - n04PositiveLeft i) ≤
          n04PositiveRight i - B.centerRight i := by
  obtain ⟨δ, hδ, hsupport⟩ :=
    n04PositiveNormalizationSupport_uniform_distance hf hK hKP
  let c : ℝ := min (1 / 8) (δ / (8 * (b - a)))
  have hc : 0 < c := lt_min (by norm_num)
    (div_pos hδ (mul_pos (by norm_num) (sub_pos.mpr hab)))
  have hc8 : c ≤ 1 / 8 := min_le_left _ _
  have hcδ : c ≤ δ / (8 * (b - a)) := min_le_right _ _
  let w : N04PositiveComponent a b f → ℝ := fun i =>
    c * (n04PositiveRight i - n04PositiveLeft i)
  have hwpos (i : N04PositiveComponent a b f) : 0 < w i :=
    mul_pos hc (sub_pos.mpr (n04PositiveComponent_bounds hf i).2.1)
  have hwsmall (i : N04PositiveComponent a b f) :
      8 * w i ≤ n04PositiveRight i - n04PositiveLeft i := by
    have h := mul_le_mul_of_nonneg_right hc8
      (sub_pos.mpr (n04PositiveComponent_bounds hf i).2.1).le
    dsimp only [w]
    nlinarith only [h]
  have hwδ (i : N04PositiveComponent a b f) : 8 * w i ≤ δ := by
    have hb := n04PositiveComponent_bounds hf i
    have hw : w i ≤ c * (b - a) :=
      mul_le_mul_of_nonneg_left (sub_le_sub hb.2.2 hb.1) hc.le
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8)
      (sub_pos.mpr hab))).mp hcδ
    nlinarith only [h, hw]
  let B : N04PositiveNormalizationBuffer a b f K := {
    centerLeft := fun i => n04PositiveLeft i + w i
    normalizationLeft := fun i => n04PositiveLeft i + 2 * w i
    normalizationRight := fun i => n04PositiveRight i - 2 * w i
    centerRight := fun i => n04PositiveRight i - w i
    ordered := by
      intro i
      have hp := hwpos i
      have hs := hwsmall i
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    support := by
      intro i x hx
      obtain ⟨hl, hr⟩ := hsupport i x hx
      have hs := hwδ i
      constructor <;> linarith }
  refine ⟨B, c, hc, ?_⟩
  intro i
  have hp : 0 ≤ c * (n04PositiveRight i - n04PositiveLeft i) := (hwpos i).le
  have hs : 8 * (c * (n04PositiveRight i - n04PositiveLeft i)) ≤
      n04PositiveRight i - n04PositiveLeft i := hwsmall i
  dsimp only [B, w]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith only [hp, hs]

end ContinuousFlexibility.Analysis
