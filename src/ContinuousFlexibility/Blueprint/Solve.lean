import ContinuousFlexibility.Blueprint.Statements

/-!
# Blueprint node Solve

The Nash–Moser iteration with quadratic error (Theorem 9.4) applied to the coupled system: one solution at a nonzero parameter.

Source: `paper/flexible-surface-readable/09-solving-the-equation.tex` lines 251–413.

Task file: `docs/tasks/Solve.md`. The statement is frozen; replace the `sorry`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem Solve (hN10 : N10Statement) (hTame : H01Statement ∧ H02Statement) : PointBranchStatement := by
  sorry

end ContinuousFlexibility.Blueprint
