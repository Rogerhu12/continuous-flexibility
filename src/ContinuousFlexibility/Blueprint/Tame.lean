import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.TameCalculusTheorem
import ContinuousFlexibility.Analysis.TameInverseTheorem

/-!
# Blueprint node Tame

Tame calculus on projective limits of Banach scales and Hamilton's theorem on families of inverses.

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 108–354;
`paper/flexible-surface-readable/09-solving-the-equation.tex` lines 251–273.

Task file: `docs/tasks/Tame.md`. The statement is frozen.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem Tame : H01Statement ∧ H02Statement := by
  exact ⟨ContinuousFlexibility.Analysis.h01Statement,
    ContinuousFlexibility.Analysis.h02Statement⟩

#print axioms Tame

end ContinuousFlexibility.Blueprint
