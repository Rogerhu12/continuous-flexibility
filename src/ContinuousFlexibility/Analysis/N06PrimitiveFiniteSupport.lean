import ContinuousFlexibility.Analysis.N06CutSaturatedSupport
import ContinuousFlexibility.Analysis.N07aAngularPieceCover

/-!
# Finite physical support on the retained canonical atlas

Primitive reference jets make the original reference intervals locally
finite. Adding both halves of each original negative component gives the
same state-independent support envelope for every actual moving cut.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n06_cutSaturatedSupport_finite_of_primitive
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : CanonicalGeometry.ReferenceJets D T S C L K)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    (n06CutSaturatedSupport C K J).Finite := by
  have href : (n06ReferenceSupportPieces K J).Finite := by
    apply (n07a_physicalPieces_finite_inter_compact hD hT h04 hjets hJ hJD).subset
    rintro m ⟨r, hr, hrJ⟩
    exact ⟨r, hrJ, hr⟩
  have hcomponents : (n06ControlSupportComponents C J).Finite :=
    n06_controlComponents_finite_on_compact hD.choose_spec.1 hC hJ hJD
  exact href.union ((hcomponents.image (fun n => (K.cutPair n).1)).union
    (hcomponents.image (fun n => (K.cutPair n).2)))

theorem n06_physicalSupportPieces_finite_of_primitive
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : CanonicalGeometry.ReferenceJets D T S C L K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    (n06PhysicalSupportPieces K z J).Finite :=
  (n06_cutSaturatedSupport_finite_of_primitive hD hT hC h04 hjets hJ hJD).subset
    (n06_physicalSupportPieces_subset_cutSaturatedSupport hC h04 hz hs J)

end ContinuousFlexibility.Statements
