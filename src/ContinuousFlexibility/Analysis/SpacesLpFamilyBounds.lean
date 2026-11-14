module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Three-term estimates for square-summable families

A pointwise estimate by three row norms lifts to the actual Hilbert-sum
norm. This separates the general norm argument from concrete jet maps.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal

theorem spaces_lp_norm_le_three {ι E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : lp (fun _ : ι => F) 2) (u v w : lp (fun _ : ι => E) 2)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C * (‖u i‖ + ‖v i‖ + ‖w i‖)) :
    ‖f‖ ≤ C * (‖u‖ + ‖v‖ + ‖w‖) := by
  let z : lp (fun _ : ι => ℝ) 2 := lp.toNorm u + lp.toNorm v + lp.toNorm w
  have hz (i : ι) : ‖z i‖ = ‖u i‖ + ‖v i‖ + ‖w i‖ := by
    change ‖‖u i‖ + ‖v i‖ + ‖w i‖‖ = _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hn : ‖f‖ ≤ ‖C • z‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro i
    change ‖f i‖ ≤ ‖C • z i‖
    rw [norm_smul, Real.norm_of_nonneg hC, hz]
    exact hf i
  calc
    ‖f‖ ≤ ‖C • z‖ := hn
    _ = C * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hC]
    _ ≤ C * (‖u‖ + ‖v‖ + ‖w‖) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans_eq
        (by simp only [lp.norm_toNorm])

end ContinuousFlexibility.Analysis
