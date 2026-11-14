import ContinuousFlexibility.Analysis.N04RealizationLeadNegativeSplit
import ContinuousFlexibility.Blueprint.N04Coordinates.Realization.NegativeGeometry.Chart
import ContinuousFlexibility.Blueprint.N04Coordinates.Realization.NegativeGeometry.Height
import ContinuousFlexibility.Blueprint.N04Coordinates.Realization.NegativeGeometry.Inverse

/-!
# N04Coordinates-Realization: negative geometry

Prove the current jets of the eight chart, inverse, height and Jacobian atoms and of the pulled height on negative pieces.

The statement is defined in
`src/ContinuousFlexibility/Analysis/N04RealizationLeadCurrentSplit.lean`.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1545-1678 (flows at a general state; Steps 1-2 of the current geometric jets lemma).
It is assembled from the three subnodes in `NegativeGeometry/` (`n04Realization_negativeGeometry_of_split`).
Task: docs/tasks/N04Realization-NegativeGeometry.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Analysis

theorem N04RealizationNegativeGeometry : N04RealizationNegativeGeometryObligation :=
  n04Realization_negativeGeometry_of_split N04RealizationNegativeChart N04RealizationNegativeHeight
    N04RealizationNegativeInverse

end ContinuousFlexibility.Blueprint
