import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.TameCalculusTheorem
import ContinuousFlexibility.Analysis.TameInverseTheorem

/-!
# Blueprint node Tame

Tame calculus on projective limits of Banach scales and Hamilton's theorem on families of inverses.

Source: `paper/flexible-surface-rewrite/07-fixed-geometry.tex` lines 102–150; `paper/flexible-surface-rewrite/08-stable-inverse.tex` lines 523–550.

Task file: `docs/tasks/Tame.md`. The statement is frozen.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem Tame : H01Statement ∧ H02Statement := by
  exact ⟨ContinuousFlexibility.Analysis.h01Statement,
    ContinuousFlexibility.Analysis.h02Statement⟩

end ContinuousFlexibility.Blueprint
