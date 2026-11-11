import ContinuousFlexibility.Analysis.N04bActualClosedTravel
import ContinuousFlexibility.Analysis.N04bRootCollarDomain

/-!
# Actual interior regularity used by the negative-piece construction
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

section Actual

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ) (side : Bool)

include hN hS hT hfield hz hs in
theorem n04b_actualRootPhysical_regular_at
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    ContDiffAt ℝ ∞
        (n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side) p ∧
      ContDiffAt ℝ ∞ (n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side) p ∧
      planeJacobian
        (n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side) p ≠ 0 ∧
      0 < n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side p := by
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hp.1.1, hp.1.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hF := (n04b_actualTravelChart_smooth hN hS hT hfield hz hs m).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  have ho := n04b_travelOrientation_pos_of_fullStrip side
    ((n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m).mapsTo hp).1
  have ha := (hfield.smooth_coefficients z hz hs).1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpD)
  have hv := (n04b_corrected_characteristics_contDiffAt hN hfield hz hs m hp).2.1
  have hap := hfield.positive_a z hz hs p hpD
  have hvp := n04b_actualCharacteristic_halfGap_pos hN hfield hz hs m hp
  refine ⟨n04b_contDiffAt_rootPhysicalChart hF ho,
    n04b_contDiffAt_rootPhysicalHeight ha hv hF hap hvp ho, ?_,
    n04bRootPhysicalHeight_pos hap hvp ho⟩
  rw [n04b_planeJacobian_rootPhysicalChart (hF.differentiableAt (by simp)) ho]
  exact mul_ne_zero (n04bRootDifferentialScale_ne_zero ho)
    (n04b_actualTravelChart_jacobian_pos hN hS hT hfield hz hs m hp).ne'

include hN hS hT hfield hz hs in
theorem n04b_actualRootPhysicalInverse_contDiffAt
    {q : PolarPoint} (hq : q.1 ∈ Ioc (0 : ℝ) (n04bRootCutRadius (C.travel m))) :
    ContDiffAt ℝ ∞
      (n04bRootPhysicalInverse (n04bActualTravelInverse S C L z m) (C.travel m) side) q := by
  have hTarget := n04b_rootStripInverse_mem_full_of_pos
    (n04b_actualTravel_positive hN hS hT hfield hz hs m) side hq
  have hX := (n04b_actualTravelInverse_spec hN hS hT hfield hz hs m).2.2.2
  exact (hX.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hTarget)).comp q
    (n04b_contDiffAt_rootStripInverse (C.travel m) side hq.1)

include hN hS hT hfield hz hs in
theorem n04b_actualRootPhysical_interior_inverse_germ
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    CanonicalBoundaryInverseGerm
      (n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side)
      (n04bRootPhysicalInverse (n04bActualTravelInverse S C L z m) (C.travel m) side) p := by
  have hX := n04b_actualTravelInverse_spec hN hS hT hfield hz hs m
  exact n04b_rootPhysical_interior_inverse_germ side
    (n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m).mapsTo
    hX.2.1 hX.2.2.1 hX.2.2.2 hp
    ((n04b_actualTravelChart_smooth hN hS hT hfield hz hs m).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp))
    (n04b_actualTravelChart_jacobian_pos hN hS hT hfield hz hs m hp).ne'

include hN hS hT hfield hz hs in
theorem n04b_actualRootPhysicalChart_continuousOn_closed :
    ContinuousOn
      (n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side)
      (Icc (C.left m) (C.right m) ×ˢ univ) :=
  (n04b_continuous_rootStripChart (C.travel m) side).comp_continuousOn
    (n04b_actualTravelChart_continuous hN hS hT hfield hz hs m)

include hN hS hT hfield hz hs in
theorem n04b_actualRootClosedInverse_continuousOn :
    ContinuousOn
      (n04bRootPhysicalInverse (n04bActualClosedTravelInverse S C L z m) (C.travel m) side)
      (Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ univ) := by
  have hTravel := n04b_actualTravel_positive hN hS hT hfield hz hs m
  apply (n04b_actualClosedTravelInverse_spec hN hS hT hfield hz hs m).2.2.2.1.comp
    (n04b_continuous_rootStripInverse (C.travel m) side).continuousOn
  intro q hq
  have hHalf := (n04b_rootStrip_closed_chart_data hTravel side).2.1 hq
  exact ⟨n04b_closedTravelHalfInterval_subset hTravel side hHalf.1, mem_univ _⟩

end Actual
end ContinuousFlexibility.Analysis
