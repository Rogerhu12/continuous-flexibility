import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Radial.R07Construction

/-!
# Blueprint node R07

One transition cell per frequency and one height sequence with all matching
angles bounded below.

Source: paper/flexible-surface-readable/05-flat-end-chain.tex, lines 790–1013.
Task file: docs/tasks/R07.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R07 (hR04 : R04Statement) (hR05 : R05Statement) (hR06 : R06Statement) : R07Statement := by
  exact Radial.r07_complete hR06

end ContinuousFlexibility.Blueprint
