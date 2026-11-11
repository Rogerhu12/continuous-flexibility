import ContinuousFlexibility.Analysis.NeighborhoodConstruction

/-!
# Blueprint node N01b

One neighbourhood of the reference state on which the type, the denominators, the flows and the charts are controlled (Lemma 7.7).

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 646–761.

Task file: `docs/tasks/N01b.md`. The node uses the actual common-neighborhood construction.
The strict-support interface repair is documented in `docs/notes/N01b-support-interface.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N01b (hN01a : N01aStatement) (hS05 : S05Statement) : N01bStatement := by
  exact n01bStatement_of_n01a hN01a

end ContinuousFlexibility.Blueprint
