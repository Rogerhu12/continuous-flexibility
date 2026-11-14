import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets

/-!
# Ordinary boundary jets determined by an open-side identity

Only infinite smoothness at the boundary point is used. For each finite
order, continuity of that actual derivative and equality in the open
side determine its boundary value. No common neighborhood of infinite
smoothness, derivative loss, or new numerical constant is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem iteratedFDeriv_eq_of_eqOn_open_of_mem_closure
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ closure U)
    (hfg : EqOn f g U) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (n : ℕ) : iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  have hfc : ContinuousAt (iteratedFDeriv ℝ n f) x :=
    (hf.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)).continuousAt
  have hgc : ContinuousAt (iteratedFDeriv ℝ n g) x :=
    (hg.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)).continuousAt
  apply sub_eq_zero.mp
  exact (hfc.sub hgc).continuousWithinAt.eq_const_of_mem_closure hx
    (fun y hy => sub_eq_zero.mpr (iteratedFDeriv_eqOn_of_isOpen hU hfg n hy))

theorem norm_iteratedFDeriv_le_of_eqOn_open_of_mem_closure
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ closure U)
    (hfg : EqOn f g U) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (n : ℕ) {M : ℝ} (hbound : ‖iteratedFDeriv ℝ n g x‖ ≤ M) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ M := by
  rw [iteratedFDeriv_eq_of_eqOn_open_of_mem_closure hU hx hfg hf hg n]
  exact hbound

end ContinuousFlexibility.Analysis
