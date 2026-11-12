import ContinuousFlexibility.Analysis.N01aFinalAssembly
import ContinuousFlexibility.Analysis.N01aGroupedReference
import ContinuousFlexibility.Analysis.N01aReferenceGoodPoints
import ContinuousFlexibility.Analysis.N01aReferenceHeight

/-!
# Blueprint node N01a

Root collars and the travel-angle controls of the reference profile (Lemmas 7.5 and 7.6).

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 506–646.

Task file: `docs/tasks/N01a.md`. The original statement is proved using the
actual weighted reference eigenfield, quantitative component enumeration,
and normalized optical travel controls.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N01a (hR12 : R12Statement) (hW01 : W01Statement) (hW02 : W02Statement) : N01aStatement := by
  obtain ⟨A⟩ := hR12
  obtain ⟨D, _, _, hindex⟩ := exists_n01a_grouped_reference A.property
  refine n01aStatement_of_quantitative_reference D hindex
    (n01a_reference_heightMember D.property) ?_ hW02
  intro p hp
  obtain ⟨B, c, N₀, hB, hc, _, hgood⟩ := exists_n01a_reference_good_points D.property hp
  exact ⟨B, c, N₀, hB, hc, hgood⟩

end ContinuousFlexibility.Blueprint

/--
info: 'ContinuousFlexibility.Blueprint.N01a' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Blueprint.N01a
