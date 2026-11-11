import ContinuousFlexibility.Statements.Milestones
import ContinuousFlexibility.Radial.MorseFullStatement

/-!
# Blueprint node R04

Source: `paper/flexible-surface-rewrite/04-designing-the-profile.tex` lines 304–377 (`eq:rad-eq-fs1`).

Task file: `docs/tasks/R04.md`. The statement is frozen.

The proof is `ContinuousFlexibility.Radial.morse_R04_statement`
(`Radial/MorseFullStatement.lean`), which proves the statement outright; the
hypothesis `R02Statement` is not needed.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R04 (_hR02 : R02Statement) : R04Statement :=
  ContinuousFlexibility.Radial.morse_R04_statement

end ContinuousFlexibility.Blueprint
