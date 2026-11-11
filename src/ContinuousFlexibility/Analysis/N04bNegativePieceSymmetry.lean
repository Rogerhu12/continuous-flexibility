import ContinuousFlexibility.Analysis.N04bNegativePieceProperties
import ContinuousFlexibility.Analysis.N04bRootHeightSymmetry

/-!
# Actual root-map symmetries used by the negative atlas

Every comparison map is the literal root transform of the actual
corrected travel chart. Periodicity and reflection are deduced from its
proved symmetries and the actual coefficient symmetries.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04b_rootAffine_component_pos
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    0 < (n04bRootAffine (if side then C.right m else C.left m) side p).1 := by
  cases side with
  | false => exact sub_pos.mpr hp.1.1
  | true => exact sub_pos.mpr hp.1.2

theorem n04b_actualNegativeDomain_subset_component
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ)
    (m : ℕ) (side : Bool) :
    n04bActualNegativeDomain S C L z m side ⊆
      Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
  fun _ hp => (mem_n04bTravelDomain.mp hp).1

section Actual

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ) (side : Bool)

theorem n04b_actualRootChart_reflection (p : PolarPoint) :
    n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side
        (p.1, -p.2) =
      ((n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
        (C.travel m) side p).1,
       -(n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
        (C.travel m) side p).2) := by
  unfold n04bRootPhysicalChart
  rw [n04b_actualTravelChart_reflection]
  rfl

include hN hS hT hfield hz hs in
theorem n04b_actualRootChart_period
    {p : PolarPoint} (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
    n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side
        (p + (0, Real.pi)) =
      n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
        (C.travel m) side p + (0, Real.pi) := by
  have ht := n04b_actualTravelChart_period_add hN hS hT hfield hz hs m hp p.2
  simpa only [n04bRootPhysicalChart, n04bRootStripChart,
    Prod.mk_add_mk, add_zero] using
    congrArg (n04bRootStripChart (C.travel m) side) ht

include hN hS hT hfield hz hs in
theorem n04b_actualRootHeight_period
    {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side (p + (0, Real.pi)) =
      n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side p := by
  have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hpD : p.1 ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hp.1.1, hp.1.2.trans (hC.1 m).2.2⟩
  obtain ⟨ha, hb, hc⟩ := hfield.periodic_coefficients z hz hs p.1 hpD
  have ha' : (L.coefficients z).a (p + (0, Real.pi)) = (L.coefficients z).a p := by
    simpa only [Prod.mk_add_mk, add_zero] using ha p.2
  have hv : n04bCharacteristicHalfGap (L.coefficients z) (p + (0, Real.pi)) =
      n04bCharacteristicHalfGap (L.coefficients z) p := by
    simpa only [Prod.mk_add_mk, add_zero] using
      (n04b_characteristic_periodic (L.coefficients z) p.1 Real.pi ha hb hc).2 p.2
  unfold n04bRootPhysicalHeight
  rw [ha', hv, n04b_actualRootChart_period hN hS hT hfield hz hs m side
    ⟨hp.1.1.le, hp.1.2.le⟩]
  simp only [Prod.fst_add, add_zero]

include hN hz hs in
theorem n04b_actualRootHeight_reflection (p : PolarPoint) :
    n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side (p.1, -p.2) =
      n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side p := by
  unfold n04bRootPhysicalHeight
  rw [(hN.2.2.2.2.1 z hz hs p.1 p.2).1,
    (n04b_actualCharacteristic_reflection hN hz hs p).2,
    n04b_actualRootChart_reflection m side p]

include hN hS hT hfield hz hs in
theorem n04b_actualRootInverse_reflection
    {q : PolarPoint}
    (hq : q ∈ Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ)) :
    n04bRootPhysicalInverse (n04bActualTravelInverse S C L z m)
        (C.travel m) side (q.1, -q.2) =
      ((n04bRootPhysicalInverse (n04bActualTravelInverse S C L z m)
        (C.travel m) side q).1,
       -(n04bRootPhysicalInverse (n04bActualTravelInverse S C L z m)
        (C.travel m) side q).2) := by
  have hpos := n04b_actualTravel_positive hN hS hT hfield hz hs m
  have hhalf := (n04b_rootStrip_chart_data hpos side).2.1 hq
  have hfull : n04bRootStripInverse (C.travel m) side q ∈
      Ioo (0 : ℝ) (C.travel m) ×ˢ (univ : Set ℝ) :=
    ⟨n04b_travelHalfInterval_subset hpos side hhalf.1, mem_univ _⟩
  exact (n04b_actualTravelInverse_symmetries hN hS hT hfield hz hs m hfull).2

end Actual

end ContinuousFlexibility.Analysis
