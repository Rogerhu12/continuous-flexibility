import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smooth tests near a matching cut

A compactly supported smooth test whose support is contained in an open
interval need not have topological support contained in that interval.
The decomposition below preserves the portions approaching the original
endpoints and isolates an interior cut in a test supported strictly
inside a prescribed neighborhood of that cut.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff

/-- Restriction to a half-line is smooth when the function vanishes near
its boundary. This single construction is used at either matching cut. -/
theorem matching_contDiff_indicator_Iio {f : ℝ → ℝ} {c : ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : f =ᶠ[𝓝 c] fun _ => 0) :
    ContDiff ℝ ∞ ((Iio c).indicator f) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  rcases lt_trichotomy x c with hx | rfl | hx
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy f
  · apply (contDiffAt_const :
      ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) c).congr_of_eventuallyEq
    filter_upwards [hc] with y hy
    simp only [Set.indicator_apply, hy, ite_self]
  · apply (contDiffAt_const :
      ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact Set.indicator_of_notMem (not_lt.mpr (le_of_lt hy)) f

/-- A cutoff equal to one near an interior point, with topological
support strictly inside a prescribed interval. -/
theorem exists_matching_cutoff {u c v : ℝ} (huc : u < c) (hcv : c < v) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo u v ∧ η =ᶠ[𝓝 c] fun _ => 1 := by
  let ε : ℝ := min (c - u) (v - c) / 3
  have hε : 0 < ε :=
    div_pos (lt_min (sub_pos.mpr huc) (sub_pos.mpr hcv)) (by norm_num)
  have hεL : 2 * ε < c - u := by
    have h := min_le_left (c - u) (v - c)
    dsimp only [ε]
    linarith only [h, huc]
  have hεR : 2 * ε < v - c := by
    have h := min_le_right (c - u) (v - c)
    dsimp only [ε]
    linarith only [h, hcv]
  let η : ContDiffBump c := ⟨ε, 2 * ε, hε, by linarith only [hε]⟩
  have hsupp : tsupport (η : ℝ → ℝ) ⊆ Ioo u v := by
    rw [η.tsupport_eq, Real.closedBall_eq_Icc]
    intro x hx
    change c - 2 * ε ≤ x ∧ x ≤ c + 2 * ε at hx
    exact ⟨by linarith only [hx.1, hεL], by linarith only [hx.2, hεR]⟩
  exact ⟨η, η.contDiff, η.hasCompactSupport, hsupp, η.eventuallyEq_one⟩

/-- Split a test into its left part, an interior cut test, and its right
part. The left and right tests retain the original endpoint behavior. -/
theorem exists_matching_cut_test_decomposition {a u c v b : ℝ}
    (huc : u < c) (hcv : c < v) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψsupp : Function.support ψ ⊆ Ioo a b) :
    ∃ ψL ψC ψR : ℝ → ℝ,
      (ContDiff ℝ ∞ ψL ∧ HasCompactSupport ψL ∧
        Function.support ψL ⊆ Ioo a c) ∧
      (ContDiff ℝ ∞ ψC ∧ HasCompactSupport ψC ∧
        tsupport ψC ⊆ Ioo u v) ∧
      (ContDiff ℝ ∞ ψR ∧ HasCompactSupport ψR ∧
        Function.support ψR ⊆ Ioo c b) ∧
      ψ = fun x => ψL x + ψC x + ψR x := by
  classical
  obtain ⟨η, hη, hηc, hηsupp, hηone⟩ := exists_matching_cutoff huc hcv
  let χ : ℝ → ℝ := fun x => (1 - η x) * ψ x
  let ψL : ℝ → ℝ := (Iio c).indicator χ
  let ψC : ℝ → ℝ := fun x => η x * ψ x
  let ψR : ℝ → ℝ := fun x => χ x - ψL x
  have hχ : ContDiff ℝ ∞ χ := (contDiff_const.sub hη).mul hψ
  have hχc : HasCompactSupport χ := by
    change HasCompactSupport ((fun x => 1 - η x) * ψ)
    exact hψc.mul_left
  have hχzero : χ =ᶠ[𝓝 c] fun _ => 0 := by
    filter_upwards [hηone] with x hx
    simp only [χ, hx, sub_self, zero_mul]
  have hχat : χ c = 0 := hχzero.eq_of_nhds
  have hL : ContDiff ℝ ∞ ψL := matching_contDiff_indicator_Iio hχ hχzero
  have hC : ContDiff ℝ ∞ ψC := hη.mul hψ
  have hR : ContDiff ℝ ∞ ψR := hχ.sub hL
  have hLsub : Function.support ψL ⊆ Function.support χ := by
    intro x hx
    change ψL x ≠ 0 at hx
    change χ x ≠ 0
    intro hz
    apply hx
    simp [ψL, Set.indicator_apply, hz]
  have hRsub : Function.support ψR ⊆ Function.support χ := by
    intro x hx
    change ψR x ≠ 0 at hx
    change χ x ≠ 0
    intro hz
    apply hx
    simp [ψR, ψL, Set.indicator_apply, hz]
  have hχsub : Function.support χ ⊆ Function.support ψ := by
    intro x hx
    change χ x ≠ 0 at hx
    change ψ x ≠ 0
    intro hz
    apply hx
    simp only [χ, hz, mul_zero]
  have hLsupp : Function.support ψL ⊆ Ioo a c := by
    intro x hx
    refine ⟨(hψsupp (hχsub (hLsub hx))).1, ?_⟩
    by_contra hxc
    apply hx
    simp [ψL, Set.indicator_apply, hxc]
  have hRsupp : Function.support ψR ⊆ Ioo c b := by
    intro x hx
    refine ⟨?_, (hψsupp (hχsub (hRsub hx))).2⟩
    by_contra hxc
    rcases lt_or_eq_of_le (le_of_not_gt hxc) with hlt | rfl
    · apply hx
      simp [ψR, ψL, Set.indicator_apply, hlt]
    · apply hx
      simp [ψR, ψL, Set.indicator_apply, hχat]
  have hCc : HasCompactSupport ψC := by
    change HasCompactSupport (η * ψ)
    exact hηc.mul_right
  have hCsupp : tsupport ψC ⊆ Ioo u v :=
    tsupport_mul_subset_left.trans hηsupp
  refine ⟨ψL, ψC, ψR, ⟨hL, hχc.mono hLsub, hLsupp⟩,
    ⟨hC, hCc, hCsupp⟩, ⟨hR, hχc.mono hRsub, hRsupp⟩, ?_⟩
  funext x
  dsimp only [ψC, ψR, χ]
  ring

end ContinuousFlexibility.Radial
