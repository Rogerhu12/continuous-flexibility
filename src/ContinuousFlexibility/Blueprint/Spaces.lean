module

public import ContinuousFlexibility.Analysis.SpacesConclusion
public import ContinuousFlexibility.Analysis.SpacesFlatFamilies

/-!
# Blueprint node Spaces

The weighted height, source and circle spaces with their tame structure, and smooth flat extension of their elements.

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 108–237 and 399–506.

Task file: `docs/tasks/Spaces.md`. The original statement is preserved.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem Spaces (hW01 : W01Statement) (hTame : H01Statement ∧ H02Statement) : W02Statement ∧ W03Statement := by
  exact ⟨spaces_W02_statement hTame.1, spaces_W03_statement⟩

end ContinuousFlexibility.Blueprint
