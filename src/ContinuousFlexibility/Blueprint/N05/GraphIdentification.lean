module

public import ContinuousFlexibility.Analysis.N05ReferenceInterface
public import ContinuousFlexibility.Analysis.N05CanonicalPhysicalL2
public import ContinuousFlexibility.Analysis.N05PhysicalCutoffUniqueness

/-!
# N05: identification of the literal physical graph

Source: readable manuscript §8, lines 234--256.
Task: `docs/tasks/N05-GraphIdentification.md`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements
open MeasureTheory

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
  obtain ⟨hγ, _, _, hphysical, _, hbase, _⟩ := hG
  have hendpoint {U : CanonicalUnknown S K} {η : PolarPoint → ℝ}
      (hW : VolumeMember S K V (3 / 4 : ℝ) (-G.lossMaterial) 0
        (fun m => U.1 m))
      (hperiodic : Function.Periodic η (0, Real.pi))
      (hrep : ∀ m, (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K (C.referenceState, 0) m
          (fun p => η p - U.2.1 * S.chiLeft p.1)) :
      MemLp (fun p : PolarPoint => Real.sqrt ((D.w p.1)⁻¹) *
        (η p - U.2.1 * S.chiLeft p.1)) 2 (radialPhysicalMeasure D) := by
    refine n05_volumeMember_canonicalHeight_endpoint_memLp
      hD.1 hT h04 hcoordinates hV (by norm_num) hW ?_ hrep
    intro p
    have he : η (p + (0, Real.pi)) = η p := hperiodic p
    have hfst : (p + ((0, Real.pi) : PolarPoint)).1 = p.1 := add_zero p.1
    change η (p + (0, Real.pi)) - U.2.1 * S.chiLeft (p + (0, Real.pi)).1 =
      η p - U.2.1 * S.chiLeft p.1
    rw [he, hfst]
  intro u F
  constructor
  · intro hrel
    obtain ⟨huVolume, η, f, huRep, hη⟩ := hrel
    obtain ⟨hbVolume, ζ, g, hbRep, hζ⟩ := hbase F
    exact n05_canonicalGraph_unique_of_endpoint_memLp
      hD.1 hS h04 hcoordinates hγ hphysical huRep hbRep hη hζ
      (hendpoint huVolume hη.1.choose_spec.2.2.1 huRep.1)
      (hendpoint hbVolume hζ.1.choose_spec.2.2.1 hbRep.1)
  · rintro rfl
    exact hbase F

/-- info: 'ContinuousFlexibility.Blueprint.N05GraphIdentification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms N05GraphIdentification

end ContinuousFlexibility.Blueprint
