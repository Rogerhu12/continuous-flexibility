import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Completion estimates for the actual graph-field cutoffs

The source cutoff errors tend to zero. A square bound for each ordered tail
therefore makes its graph fields Cauchy, without changing the ambient L2
space or assuming a priori regularity of the source representative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology BigOperators

/-- An ordered square-tail estimate controlled by vanishing nonnegative errors
gives Cauchy convergence in the original normed group. -/
theorem n06_cauchySeq_of_sq_norm_sub_le_errors
    {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → E) (e : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (he : ∀ n, 0 ≤ e n) (hlim : Tendsto e atTop (𝓝 0))
    (hbound : ∀ N M : ℕ, N ≤ M →
      ‖f M - f N‖ ^ 2 ≤ C * (2 * e N + 2 * e M)) : CauchySeq f := by
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  let δ : ℝ := ε ^ 2 / (4 * (C + 1))
  have hCp : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) (mul_pos (by norm_num) hCp)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  have herr : 2 * e N + 2 * e n < 4 * δ := by
    linarith only [hN N le_rfl, hN n hn]
  have hslack : C * (2 * e N + 2 * e n) ≤
      (C + 1) * (2 * e N + 2 * e n) :=
    mul_le_mul_of_nonneg_right (by linarith)
      (add_nonneg (mul_nonneg (by norm_num) (he N)) (mul_nonneg (by norm_num) (he n)))
  have hstrict := mul_lt_mul_of_pos_left herr hCp
  have hδeq : (C + 1) * (4 * δ) = ε ^ 2 := by
    dsimp only [δ]
    field_simp [hCp.ne']
    <;> ring
  rw [hδeq] at hstrict
  have hsq : ‖f n - f N‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt ((hbound N n hn).trans hslack) hstrict
  rw [dist_eq_norm]
  exact (sq_lt_sq₀ (norm_nonneg (f n - f N)) hε.le).mp hsq

/-- A vanishing finite row of squared norm errors gives strong convergence
of every component, in precisely its original norm. -/
theorem n06_tendsto_component_of_sum_sq_errors
    {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    {f : ℕ → ι → E} {g : ι → E}
    (hlim : Tendsto (fun N => ∑ i, ‖f N i - g i‖ ^ 2) atTop (𝓝 0)) (i : ι) :
    Tendsto (fun N => f N i) atTop (𝓝 (g i)) := by
  have hs : Tendsto (fun N => ‖f N i - g i‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _)
      (fun N => Finset.single_le_sum (fun j _ => sq_nonneg ‖f N j - g j‖)
        (Finset.mem_univ i)) hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt

/-- Norm-square sums pass to the limit for any fixed finite row. -/
theorem n06_tendsto_sum_sq_norm
    {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    {f : ℕ → ι → E} {g : ι → E}
    (hlim : ∀ i, Tendsto (fun N => f N i) atTop (𝓝 (g i))) :
    Tendsto (fun N => ∑ i, ‖f N i‖ ^ 2) atTop (𝓝 (∑ i, ‖g i‖ ^ 2)) :=
  tendsto_finsetSum Finset.univ (fun i _ => (hlim i).norm.pow 2)

end ContinuousFlexibility.Analysis
