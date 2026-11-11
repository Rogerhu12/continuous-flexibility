import ContinuousFlexibility.Analysis.N04FlowJetsTarget

/-!
# N04Coordinates: actual mixed-parameter flow estimates

This subnode proves the quantitative flow tool used by the controlled
coordinate construction. The target fixes one low state order and one
loss before every derivative order. It bounds actual Frechet derivatives
of an actual periodic scalar flow, with the angular Gronwall exponent
separate from the large material-dependent parameter derivatives.

Source: paper/flexible-surface-readable/07-fixed-geometry.tex,
the general-state flow and geometric-jet lemmas, lines 1531–1703.
Task: docs/tasks/N04Coordinates-FlowJets.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04CoordinatesFlowJets : N04FlowJetsTarget := by
  sorry

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.N04CoordinatesFlowJets
