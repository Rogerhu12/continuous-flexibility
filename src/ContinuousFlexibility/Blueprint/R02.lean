module

public import ContinuousFlexibility.Statements.Milestones
public import ContinuousFlexibility.Radial.GeneralLiouvilleTransport

/-!
# Blueprint node R02

Source: `paper/flexible-surface-rewrite/04-designing-the-profile.tex` lines 118–137 (`eq:rad-eq-sc0`); `paper/flexible-surface-rewrite/04-designing-the-profile.tex` lines 272–301 (`eq:rad-eq-ha2`).

Task file: `docs/tasks/R02.md`. The statement is frozen.

The proof is `ContinuousFlexibility.Radial.generalLiouville_R02_statement`, the
Liouville transport on the actual open range of each positive increasing radius.
It does not need the hypothesis `R01Statement`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R02 (_hR01 : R01Statement) : R02Statement :=
  ContinuousFlexibility.Radial.generalLiouville_R02_statement

end ContinuousFlexibility.Blueprint
