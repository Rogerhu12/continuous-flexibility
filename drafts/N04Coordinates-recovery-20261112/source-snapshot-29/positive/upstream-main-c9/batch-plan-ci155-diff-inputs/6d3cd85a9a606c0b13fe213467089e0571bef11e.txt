import ContinuousFlexibility.Blueprint.N01c.Coefficients
import ContinuousFlexibility.Blueprint.N01c.Speeds
import ContinuousFlexibility.Blueprint.N01c.Flows

/-!
# Blueprint node N01c

The tame bounds of the coefficient and flow families on that neighbourhood (part of Proposition 7.8).

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 761–806; `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1303–1725.

Task file: `docs/tasks/N01c.md`.  The large node is assembled from three
concrete stages.  This assembly is not a closed proof until all three leaves
pass the axiom audit.  The flow loss now follows the manuscript's `d_k`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N01c (hN01b : N01bStatement) : N01Statement := by
  exact N01cFlows (N01cSpeeds (N01cCoefficients hN01b))

end ContinuousFlexibility.Blueprint
