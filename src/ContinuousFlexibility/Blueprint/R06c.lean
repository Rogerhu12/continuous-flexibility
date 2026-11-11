import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Radial.DeepTailPhysicalPipeline
import ContinuousFlexibility.Radial.DeepTailParameterPipeline

/-!
# Blueprint node R06c

Deep tail: flatness in the original radius, the source identity, and continuity in the height ratios.

Source: `paper/flexible-surface-rewrite/05-flat-end-chain.tex` lines 443–505.

Task file: `docs/tasks/R06c.md`. The exact statement is preserved.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R06c : R06cStatement := by
  intro C η K hC hη hη₁ hK hfull
  let η' : ℝ := min η (1 / 16)
  let K' : ℝ := max K 64
  have hη' : 0 < η' := lt_min hη (by norm_num)
  have hη'₁ : η' < 1 := (min_le_left _ _).trans_lt hη₁
  have hK' : 1 < K' := hK.trans_le (le_max_left _ _)
  have hfull' : R06Full C η' K' :=
    r06Full_mono hfull (min_le_left _ _) (le_max_left _ _)
  have hsmall : η' ≤ 1 / 16 := min_le_right _ _
  have hlarge : 64 ≤ K' := le_max_right _ _
  refine ⟨C, η', K', hC, hη', hη'₁, hK', hfull', ?_, ?_⟩
  · exact r06Physical_of_r06Full hfull' (hsmall.trans (by norm_num))
  · exact r06Parameter_of_r06Full hfull' hsmall hlarge

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.R06c
