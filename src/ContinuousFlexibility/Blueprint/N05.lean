module

public import ContinuousFlexibility.Blueprint.N05.ReferenceGeometry
public import ContinuousFlexibility.Blueprint.N05.VolumeModel
public import ContinuousFlexibility.Blueprint.N05.InverseBounds
public import ContinuousFlexibility.Blueprint.N05.GraphIdentification
public import ContinuousFlexibility.Analysis.N05ReferenceAssembly

/-!
# Blueprint node N05

The canonical reference inverse on the two-weight volume spaces and its closed common domain.

Source: `paper/flexible-surface-rewrite/08-stable-inverse.tex` lines 14–171.

Task file: `docs/tasks/N05.md`. The frozen statement is assembled from the
explicit sub-blueprint. Completion also requires closing every sub-statement.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N05 (hN04 : N04Statement) : N05Statement := by
  obtain ⟨A, T, S, C, R, L, K, base, loss, ε, hT, hS, h04, hcoordinates⟩ :=
    N05ReferenceGeometry hN04
  obtain ⟨V, hV⟩ := N05VolumeModel A.property.1 hT S K
  obtain ⟨G, hG⟩ := N05InverseBounds A.property hT hS h04 hcoordinates hV
  have hR := N05GraphIdentification A.property hT hS h04 hcoordinates hV G hG
  exact ⟨A, T, S, C, R, L, K, V, 2, n05ReferenceDomain G hR,
    base, loss, ε, hT, hS, h04, n05ReferenceDomain_properties G hR hV hG⟩

/-- info: 'ContinuousFlexibility.Blueprint.N05' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms N05

end ContinuousFlexibility.Blueprint
