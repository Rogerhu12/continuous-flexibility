import ContinuousFlexibility.Statements.Milestones
import ContinuousFlexibility.Radial.CentralFullStatement

/-!
# Blueprint node R03

Source: `paper/flexible-surface-rewrite/04-designing-the-profile.tex` lines 177–301 (`eq:central-spectrum-new`).

Task file: `docs/tasks/R03.md`. The statement is frozen. Proved.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R03 (_hR02 : R02Statement) : R03Statement :=
  Radial.centralR03_statement

end ContinuousFlexibility.Blueprint
