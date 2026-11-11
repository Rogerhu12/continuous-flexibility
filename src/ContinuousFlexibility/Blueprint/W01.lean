import ContinuousFlexibility.Statements.Milestones
import ContinuousFlexibility.Analysis.AffineMaterialFull

/-!
# Blueprint node W01

Source: `paper/flexible-surface-rewrite/07-fixed-geometry.tex` lines 22–59. Proved.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem W01 : W01Statement :=
  ContinuousFlexibility.Statements.affineMaterial_W01_statement

end ContinuousFlexibility.Blueprint
