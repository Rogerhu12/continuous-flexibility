module

public import ContinuousFlexibility.Analysis.N05CanonicalInverseBounds

/-!
# N05: the same reference inverse on all weighted volume levels

Source: readable manuscript §8, lines 75--167 and 169--233.
Task: `docs/tasks/N05-InverseBounds.md`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N05InverseBounds {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h04 : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V) :
    ∃ G : N05ReferenceInverseData S K V, N05ReferenceInverseBounds D T S C K V G := by
  exact n05_existsReferenceInverseBounds hD hT hS h04 hcoordinates hV

/-- info: 'ContinuousFlexibility.Blueprint.N05InverseBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms N05InverseBounds

end ContinuousFlexibility.Blueprint
