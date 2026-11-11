import ContinuousFlexibility.Scalar.WeightedRealization

/-!
# Blueprint node ScalarWeighted

The three weighted scalar milestones on the actual physical spaces,
including one common low-order neighborhood and the flat endpoints.

Source: `paper/flexible-surface-readable/03-height-equation.tex` lines 406–543;
`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 108–506.

Task file: `docs/tasks/ScalarWeighted.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem ScalarWeighted : S03WeightedStatement ∧ S04WeightedStatement ∧ S05WeightedStatement :=
  ContinuousFlexibility.Statements.scalarWeighted

end ContinuousFlexibility.Blueprint
