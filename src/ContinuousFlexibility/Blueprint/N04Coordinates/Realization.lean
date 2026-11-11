import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.N04FlowJetsTarget

/-!
# N04Coordinates: controlled coordinate realization

Use the actual mixed-parameter flow theorem to construct coordinates,
their inverses and height factors on one state neighborhood, retaining
N01–N03 and both qualitative canonical parts. Derive the actual potential
and divided-coefficient estimates and the source-pairing identity.

The conclusion is exactly the frozen N04c statement. The additional
subnode input is an independently stated ODE theorem about arbitrary
raw periodic fields; no canonical estimate is assumed.

Source: paper/flexible-surface-readable/07-fixed-geometry.tex,
the root, positive-component and uniform-geometry constructions,
in particular lines 1211–1725.
Task: docs/tasks/N04Coordinates-Realization.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04CoordinatesRealization
    (hFlowJets : N04FlowJetsTarget) (hN04b : N04bStatement) : N04cStatement := by
  sorry

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.N04CoordinatesRealization
