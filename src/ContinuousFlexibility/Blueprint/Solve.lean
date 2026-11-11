import ContinuousFlexibility.Blueprint.Statements

/-!
# Blueprint node Solve

The coupled inverse, the exact quadratic error, the Nash–Moser iteration, and one solution at a nonzero parameter.

Source: `paper/flexible-surface-rewrite/09-solving-the-equation.tex` lines 139–242.

Task file: `docs/tasks/Solve.md`. The statement is frozen; replace the `sorry`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem Solve (hN08 : N08Statement) (hTame : H01Statement ∧ H02Statement) : PointBranchStatement := by
  sorry

end ContinuousFlexibility.Blueprint
