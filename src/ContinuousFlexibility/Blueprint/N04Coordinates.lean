import ContinuousFlexibility.Blueprint.N04Coordinates.FlowJets
import ContinuousFlexibility.Blueprint.N04Coordinates.Realization

/-!
# Blueprint node N04Coordinates

The exact frozen implication is assembled from the genuine mixed-flow
estimate and the controlled coordinate realization. The subnodes remain
explicit proof obligations until their axiom audits contain no sorryAx.

Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1497–1760.
Task: docs/tasks/N04Coordinates.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04Coordinates (hN04b : N04bStatement) : N04cStatement :=
  N04CoordinatesRealization N04CoordinatesFlowJets hN04b

end ContinuousFlexibility.Blueprint
