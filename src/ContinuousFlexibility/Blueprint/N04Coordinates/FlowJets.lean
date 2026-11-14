module

public import ContinuousFlexibility.Analysis.N04FlowJetsProof

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

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04CoordinatesFlowJets : N04FlowJetsTarget :=
  ContinuousFlexibility.Analysis.n04FlowJetsTarget_proof

end ContinuousFlexibility.Blueprint

/--
info: 'ContinuousFlexibility.Blueprint.N04CoordinatesFlowJets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Blueprint.N04CoordinatesFlowJets
