import ContinuousFlexibility.Analysis.N04bActualTypedAtlas

/-!
# Part A for the actual corrected characteristic atlas

The final record uses the genuine constructed negative functions and
the already proved positive Liouville functions. Every geometric clause
is proved for that record: moving-domain partition, optical reference
metadata, normalization, both open and closed inverses, smooth boundary
germs, angular period and reflection.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04b_actualTypedAtlas_partA
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) :
    CanonicalGeometry D S C (n04bActualTypedAtlas hT hS hN hfield e) base ε := by
  let hD := n04b_profileGeometry_of_through03 hN
  let hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  let cut := n04bActualReferenceCut hN
  let F := n04bActualNegativeChart hT hS hN hfield
  let h := n04bActualNegativeHeight hT hS hN hfield
  let J := n04bActualNegativeInverse hT hS hN hfield
  have hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m) :=
    n04bActualReferenceCut_mem hN
  have hborder : RadialTrueBorder D := hN.1.1.1.2.2.2.1
  change CanonicalGeometry D S C (n04bTypedAtlasData D S C L cut e F h J) base ε
  refine
    { normalizationOpen := ?_
      normalizationSupport := ?_
      normalization := ?_
      referenceBounds := ?_
      referencePositive := ?_
      referenceNegative := ?_
      referencePartition := ?_
      referenceDomain := ?_
      domains := ?_
      partition := ?_
      charts := ?_
      boundary := ?_
      reflection := ?_
      inverseReflection := ?_ }
  · exact n04bNormalizationRegion_isOpen D
  · exact n04b_referenceColumn_support_normalizationRegion hD hborder
  · intro z hz hs m
    exact n04bTypedAtlasData_normalization e F h J hC cut z m
  · exact n04bTypedAtlasData_referenceBounds e F h J hD hC cut hcut
  · exact n04bTypedAtlasData_referencePositive e F h J hD hC cut hcut
  · exact n04bTypedAtlasData_referenceNegative e F h J hD hC cut hcut
  · exact n04bTypedAtlasData_referencePartition e F h J hD hC cut hcut
  · exact n04bTypedAtlasData_referenceDomain e F h J hD hC hN.1.1.2.2.1 hfield
  · intro z hz hs m
    exact n04bTypedAtlasData_domains e F h J hT hS hN hfield hD hC hz hs m
  · intro z hz hs
    exact n04bTypedAtlasData_partition e F h J hT hS hN hfield cut hz hs
  · intro z hz hs k
    cases hi : e k with
    | inl i =>
      rcases i with ⟨m, side⟩
      exact n04bTypedAtlasData_negative_charts e F h J cut k m side hi
        hN hS hT hfield hz hs (n04bActualNegativeFunctions_spec hT hS hN hfield hz hs m side)
    | inr i =>
      exact n04bTypedAtlasData_positive_charts e F h J hD hC cut hcut hz hs k i hi
  · intro z hz hs k
    cases hi : e k with
    | inl i =>
      rcases i with ⟨m, side⟩
      exact n04bTypedAtlasData_negative_boundary e F h J cut k m side hi
        hN hS hT hfield hz hs (n04bActualNegativeFunctions_spec hT hS hN hfield hz hs m side)
    | inr i =>
      exact n04bTypedAtlasData_positive_boundary e F h J hD hC cut hcut hz hs k i hi
  · intro z hz hs k
    cases hi : e k with
    | inl i =>
      rcases i with ⟨m, side⟩
      exact n04bTypedAtlasData_negative_reflection e F h J cut k m side hi
        hN hS hT hfield hz hs (n04bActualNegativeFunctions_spec hT hS hN hfield hz hs m side)
    | inr i =>
      exact n04bTypedAtlasData_positive_reflection e F h J hD hC cut hcut hz hs k i hi
  · intro z hz hs k
    cases hi : e k with
    | inl i =>
      rcases i with ⟨m, side⟩
      exact n04bTypedAtlasData_negative_inverseReflection e F h J cut k m side hi
        hN hS hT hfield hz hs (n04bActualNegativeFunctions_spec hT hS hN hfield hz hs m side)
    | inr i =>
      exact n04bTypedAtlasData_positive_inverseReflection e F h J hD hC cut hcut hz hs k i hi

end ContinuousFlexibility.Analysis
