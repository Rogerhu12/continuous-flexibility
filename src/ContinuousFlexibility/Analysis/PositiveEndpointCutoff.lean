module

public import ContinuousFlexibility.Analysis.BoundaryTaylorExtension
public import Mathlib.Topology.Algebra.Support

/-!
# Small endpoint cutoffs for the positive reference construction

Copies of one fixed bump may be placed in arbitrarily small endpoint
collars. Their closed supports lie strictly inside those collars. This
allows a field smooth on the actual collar to be clipped into a globally
smooth field, without assuming a common smooth neighborhood from a
single pointwise smoothness hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The fixed Taylor cutoff at an independently chosen endpoint scale. -/
def positiveEndpointCutoff (c δ x : ℝ) : ℝ :=
  boundaryTaylorCutoff ((x - c) / δ)

theorem contDiff_positiveEndpointCutoff (c δ : ℝ) :
    ContDiff ℝ ∞ (positiveEndpointCutoff c δ) :=
  boundaryTaylorCutoff.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const δ)

theorem positiveEndpointCutoff_nonneg (c δ x : ℝ) :
    0 ≤ positiveEndpointCutoff c δ x :=
  boundaryTaylorCutoff.nonneg

theorem positiveEndpointCutoff_le_one (c δ x : ℝ) :
    positiveEndpointCutoff c δ x ≤ 1 :=
  boundaryTaylorCutoff.le_one

theorem positiveEndpointCutoff_one_germ (c δ : ℝ) :
    positiveEndpointCutoff c δ =ᶠ[𝓝 c] 1 := by
  have hcont : Continuous (fun x : ℝ => (x - c) / δ) :=
    (continuous_id.sub continuous_const).div_const δ
  have hlim : Tendsto (fun x : ℝ => (x - c) / δ) (𝓝 c) (𝓝 0) := by
    simpa only [sub_self, zero_div] using hcont.tendsto c
  exact boundaryTaylorCutoff.eventuallyEq_one.comp_tendsto hlim

/-- The closed support is strictly inside the prescribed collar. -/
theorem tsupport_positiveEndpointCutoff_subset_ball
    {c δ : ℝ} (hδ : 0 < δ) :
    tsupport (positiveEndpointCutoff c δ) ⊆ Metric.ball c δ := by
  have hcont : Continuous (fun x : ℝ => (x - c) / δ) :=
    (continuous_id.sub continuous_const).div_const δ
  have hs := tsupport_comp_subset_preimage
    (boundaryTaylorCutoff : ℝ → ℝ) hcont
  intro x hx
  have hx' : x ∈ tsupport
      ((boundaryTaylorCutoff : ℝ → ℝ) ∘ fun y : ℝ => (y - c) / δ) := hx
  have ht := hs hx'
  change (x - c) / δ ∈ tsupport (boundaryTaylorCutoff : ℝ → ℝ) at ht
  rw [boundaryTaylorCutoff.tsupport_eq] at ht
  have hratio : |(x - c) / δ| ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero,
      boundaryTaylorCutoff] using ht
  rw [abs_div, abs_of_pos hδ] at hratio
  have hdist := (div_le_iff₀ hδ).mp hratio
  rw [Metric.mem_ball, Real.dist_eq]
  nlinarith

theorem positiveEndpointCutoff_zero_germ_of_not_mem_ball
    {c δ x : ℝ} (hδ : 0 < δ) (hx : x ∉ Metric.ball c δ) :
    positiveEndpointCutoff c δ =ᶠ[𝓝 x] 0 :=
  notMem_tsupport_iff_eventuallyEq.mp
    (fun h => hx (tsupport_positiveEndpointCutoff_subset_ball hδ h))

theorem positiveEndpointCutoff_eq_zero_of_not_mem_ball
    {c δ x : ℝ} (hδ : 0 < δ) (hx : x ∉ Metric.ball c δ) :
    positiveEndpointCutoff c δ x = 0 :=
  (positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ hx).eq_of_nhds

theorem positiveEndpointCutoff_zero_germ_of_separation
    {c d δ : ℝ} (hδ : 0 < δ) (hcd : δ ≤ |c - d|) :
    positiveEndpointCutoff d δ =ᶠ[𝓝 c] 0 := by
  apply positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ
  simpa only [Metric.mem_ball, Real.dist_eq, not_lt] using hcd

/-- Local smoothness on the full open collar is enough after clipping. -/
theorem contDiff_positiveEndpointCutoff_mul
    {c δ : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ)
    (hf : ∀ x ∈ Metric.ball c δ, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (fun x => positiveEndpointCutoff c δ x * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport (positiveEndpointCutoff c δ)
  · exact (contDiff_positiveEndpointCutoff c δ).contDiffAt.mul
      (hf x (tsupport_positiveEndpointCutoff_subset_ball hδ hx))
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have hzero : (fun y => positiveEndpointCutoff c δ y * f y) =ᶠ[𝓝 x]
        (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hz] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-- Bounds on the collar control the clipped field on the entire line. -/
theorem abs_positiveEndpointCutoff_mul_le
    {c δ M : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Metric.ball c δ, |f x| ≤ M) (x : ℝ) :
    |positiveEndpointCutoff c δ x * f x| ≤ M := by
  by_cases hx : x ∈ Metric.ball c δ
  · rw [abs_mul, abs_of_nonneg (positiveEndpointCutoff_nonneg c δ x)]
    exact (mul_le_mul (positiveEndpointCutoff_le_one c δ x)
      (hf x hx) (abs_nonneg _) (by norm_num)).trans_eq (one_mul M)
  · rw [positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hx,
      zero_mul, abs_zero]
    exact hM

/-- A lower bound for the endpoint slope survives multiplication by the
nonnegative cutoff. No condition is imposed on the slope outside the collar. -/
theorem positiveEndpointCutoff_mul_lower
    {c δ A : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ)
    (hf : ∀ x ∈ Metric.ball c δ, A ≤ f x) (x : ℝ) :
    A * positiveEndpointCutoff c δ x ≤
      positiveEndpointCutoff c δ x * f x := by
  by_cases hx : x ∈ Metric.ball c δ
  · simpa only [mul_comm A] using
      mul_le_mul_of_nonneg_left (hf x hx)
        (positiveEndpointCutoff_nonneg c δ x)
  · simp only [positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hx,
      mul_zero, zero_mul, le_refl]

theorem disjoint_tsupport_positiveEndpointCutoff
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l) :
    Disjoint (tsupport (positiveEndpointCutoff l δ))
      (tsupport (positiveEndpointCutoff r δ)) := by
  apply Set.disjoint_left.mpr
  intro x hxL hxR
  have hxL' := tsupport_positiveEndpointCutoff_subset_ball hδ hxL
  have hxR' := tsupport_positiveEndpointCutoff_subset_ball hδ hxR
  rw [Metric.mem_ball, Real.dist_eq] at hxL' hxR'
  have htri := abs_sub_le r x l
  rw [abs_sub_comm r x, abs_of_nonneg (by linarith : 0 ≤ r - l)] at htri
  linarith

theorem positiveEndpointCutoff_add_le_one
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l) (x : ℝ) :
    positiveEndpointCutoff l δ x + positiveEndpointCutoff r δ x ≤ 1 := by
  by_cases hxL : positiveEndpointCutoff l δ x = 0
  · simpa only [hxL, zero_add] using positiveEndpointCutoff_le_one r δ x
  · have hxLs : x ∈ tsupport (positiveEndpointCutoff l δ) :=
      subset_tsupport _ (Function.mem_support.mpr hxL)
    have hxRs : x ∉ tsupport (positiveEndpointCutoff r δ) :=
      fun hx => (Set.disjoint_left.mp
        (disjoint_tsupport_positiveEndpointCutoff hδ hgap)) hxLs hx
    have hz := image_eq_zero_of_notMem_tsupport hxRs
    simpa only [hz, add_zero] using positiveEndpointCutoff_le_one l δ x

/-- A closed forbidden set missing both endpoints leaves arbitrarily small
disjoint endpoint collars. The radius is allowed to depend on the component. -/
theorem exists_positiveEndpoint_collars_avoiding
    {F : Set ℝ} (hF : IsClosed F) {l r ε : ℝ}
    (hl : l ∉ F) (hr : r ∉ F) (hlr : l < r) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ 2 * δ < r - l ∧
      Disjoint (Metric.ball l δ) F ∧ Disjoint (Metric.ball r δ) F := by
  obtain ⟨δL, hδL, hL⟩ := Metric.mem_nhds_iff.mp
    (hF.isOpen_compl.mem_nhds hl)
  obtain ⟨δR, hδR, hR⟩ := Metric.mem_nhds_iff.mp
    (hF.isOpen_compl.mem_nhds hr)
  have hsmall : 0 < min (min δL δR) (min ε ((r - l) / 2)) :=
    lt_min (lt_min hδL hδR) (lt_min hε (by linarith))
  obtain ⟨δ, hδ, hδsmall⟩ := exists_between hsmall
  have hδL' : δ < δL :=
    hδsmall.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδR' : δ < δR :=
    hδsmall.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδε : δ < ε :=
    hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδgap : δ < (r - l) / 2 :=
    hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδ, hδε, by linarith, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hxF
    exact (hL (Metric.ball_subset_ball hδL'.le hx)) hxF
  · apply Set.disjoint_left.mpr
    intro x hx hxF
    exact (hR (Metric.ball_subset_ball hδR'.le hx)) hxF

end ContinuousFlexibility.Analysis
