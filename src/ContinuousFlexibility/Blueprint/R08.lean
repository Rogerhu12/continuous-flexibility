import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Radial.SeedReferenceTheorem

/-!
# Blueprint node R08

Joining the central model to the selected tails while keeping the second-mode solution.

Source: paper/flexible-surface-readable/06-global-reference-inverse.tex, lines 100–180.

Task file: docs/tasks/R08.md. The milestone statement is unchanged.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R08 (hR03 : R03Statement) (hR07 : R07Statement) : R08Statement :=
  ContinuousFlexibility.Radial.seedReference_theorem hR03 hR07

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.R08
