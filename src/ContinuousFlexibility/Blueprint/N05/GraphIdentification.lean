import ContinuousFlexibility.Analysis.N05ReferenceInterface

/-!
# N05: identification of the literal physical graph

Source: readable manuscript §8, lines 234--256.
Task: `docs/tasks/N05-GraphIdentification.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N05GraphIdentification {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h04 : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V)
    (G : N05ReferenceInverseData S K V)
    (hG : N05ReferenceInverseBounds D T S C K V G) :
    ∀ u F, ReferenceCanonicalRelation D T S C K V G.weakExponent
      G.sourceMaterial G.outputMaterial G.lossMaterial u
        (V.forget (3 / 4 : ℝ) 0 2 F) ↔ u = G.baseInverse F := by
  sorry

end ContinuousFlexibility.Blueprint
