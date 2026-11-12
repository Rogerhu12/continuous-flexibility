import ContinuousFlexibility.Analysis.N01aFinalAssembly
import ContinuousFlexibility.Analysis.N01cActualN01aReference
import ContinuousFlexibility.Analysis.N01aReferenceHeight

/-!
# Blueprint node N01a

Root collars, normalized travel controls and primitive geometry on the
same actual retained reference, with the controls' actual host cells.

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 506–646.
Task file: `docs/tasks/N01a.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N01a (hR12 : R12Statement) (hW01 : W01Statement) (hW02 : W02Statement) : N01aStatement := by
  obtain ⟨D, hprimitive, henumerate⟩ := exists_n01c_actual_n01a_reference
  exact n01aStatement_of_quantitative_reference D hprimitive henumerate
    (n01a_reference_heightMember D.property) hW02

end ContinuousFlexibility.Blueprint

/--
info: 'ContinuousFlexibility.Blueprint.N01a' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Blueprint.N01a
