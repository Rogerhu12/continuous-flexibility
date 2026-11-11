import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Radial.PositiveBufferR09

/-!
# Blueprint node R09

Cutting a model inverse inside a positive buffer.

Source: `paper/flexible-surface-readable/06-global-reference-inverse.tex` lines 180–352.
Task file: `docs/tasks/R09.md`.

The proof constructs the actual interval inverse, endpoint profiles,
Poisson columns and conormal estimates with the frozen statement.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R09 : R09Statement :=
  ContinuousFlexibility.Radial.r09Statement

end ContinuousFlexibility.Blueprint

/--
info: 'ContinuousFlexibility.Blueprint.R09' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Blueprint.R09
