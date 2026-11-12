import ContinuousFlexibility.Analysis.N04bActualTypedAtlas
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient
import ContinuousFlexibility.Analysis.N07aCurrentPhysicalGeometry

/-!
# A moving negative point in the fixed reference partition

The old optical cut is retained as a separate case. Away from it, the
same component supplies a reference half and its genuine affine inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- A point of either actual moving half is either on the old reference
cut or is a physical unit point of one reference half of the same component. -/
theorem n04bActualTypedAtlas_moving_negative_reference_unitPoint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (z : AnnularState S × ℝ)
    (m : ℕ) (side : Bool) (p : PolarPoint) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    p ∈ physicalPieceOpen S K z (e.symm (.inl (m, side))) →
      p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) ∧
      (p.1 = n04bActualReferenceCut hN m ∨
        ∃ refSide : Bool,
          (if refSide then n04bActualReferenceCut hN m < p.1
            else p.1 < n04bActualReferenceCut hN m) ∧
          let j := e.symm (.inl (m, refSide))
          let q := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) j p
          p ∈ referencePhysicalPieceOpen S K j ∧
            q ∈ CanonicalGeometry.unitStrip ∧
            CanonicalGeometry.physicalUnitPoint K j q = p) := by
  classical
  intro K hp
  have hp' : p ∈ n04bTypedPhysicalDomain (D := D) C
      (n04bActualTravelChart S C L z) (.inl (m, side)) := by
    simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_physicalPieceOpen,
      Equiv.apply_symm_apply] using hp
  have hfull := n04b_typed_negative_domain_subset (m, side) hp'
  refine ⟨hfull, ?_⟩
  by_cases hcut : p.1 = n04bActualReferenceCut hN m
  · exact Or.inl hcut
  · right
    have hex : ∃ t : Bool,
        (if t then n04bActualReferenceCut hN m < p.1
          else p.1 < n04bActualReferenceCut hN m) ∧
        p ∈ Ioo (n04bNegativeLeft C (n04bActualReferenceCut hN) (m, t))
          (n04bNegativeRight C (n04bActualReferenceCut hN) (m, t)) ×ˢ univ := by
      rcases lt_or_gt_of_ne hcut with hl | hr
      · exact ⟨false, hl, ⟨hfull.1.1, hl⟩, mem_univ _⟩
      · exact ⟨true, hr, ⟨hr, hfull.1.2⟩, mem_univ _⟩
    obtain ⟨refSide, hside, hr⟩ := hex
    have href : p ∈ referencePhysicalPieceOpen S K (e.symm (.inl (m, refSide))) := by
      simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_referencePhysicalPieceOpen,
        Equiv.apply_symm_apply, n04bReferenceTypedLeft, n04bReferenceTypedRight] using hr
    have hwidth : K.physicalLeft (e.symm (.inl (m, refSide))) <
        K.physicalRight (e.symm (.inl (m, refSide))) := href.1.1.trans href.1.2
    exact ⟨refSide, hside, href,
      n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData K) hwidth href,
      n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K) hwidth p⟩

end ContinuousFlexibility.Analysis
