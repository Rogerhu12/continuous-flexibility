module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Analysis.CubicDivisionL2

/-!
# Blueprint node N04Cubic

Division by y³ of a function vanishing to third order, in L² with three derivatives lost.

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1211–1303.

Task file: `docs/tasks/N04Cubic.md`. The frozen statement is proved with the
uniform constant eight, using three applications of the Euler L² estimate.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04Cubic : CubicDivisionTarget := by
  intro s
  refine ⟨8, by norm_num, ?_⟩
  intro f hf hf0 hf1 hf2
  exact ⟨(contDiff_cubicQuotient hf hf0 hf1 hf2).contDiffOn,
    eLpNorm_iteratedDeriv_cubicQuotient hf hf0 hf1 hf2 s⟩

/--
info: 'ContinuousFlexibility.Blueprint.N04Cubic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms N04Cubic

end ContinuousFlexibility.Blueprint
