import ContinuousFlexibility.Blueprint.Statements

/-!
# Blueprint node ScalarCalculus

The pointwise and finite-rectangle calculus of the height equation: connection, residual, conservation, type correction.

Source: `paper/flexible-surface-rewrite/03-height-equation.tex` lines 11–106; `paper/flexible-surface-rewrite/03-height-equation.tex` lines 287–376.

Task file: `docs/tasks/ScalarCalculus.md`. The statement is frozen; replace the `sorry`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem ScalarCalculus : S03CalculusStatement ∧ S04CalculusStatement ∧ S05CalculusStatement := by
  sorry

end ContinuousFlexibility.Blueprint
