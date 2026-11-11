import ContinuousFlexibility.Blueprint.Statements

/-!
# Blueprint node ScalarWeighted

The same three statements on the weighted function spaces, up to the flat endpoints.

Source: `paper/flexible-surface-rewrite/03-height-equation.tex` lines 287–376; `paper/flexible-surface-rewrite/07-fixed-geometry.tex` lines 72–157.

Task file: `docs/tasks/ScalarWeighted.md`. The statement is frozen; replace the `sorry`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem ScalarWeighted : S03WeightedStatement ∧ S04WeightedStatement ∧ S05WeightedStatement := by
  sorry

end ContinuousFlexibility.Blueprint
