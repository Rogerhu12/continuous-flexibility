import ContinuousFlexibility.Analysis.N04bNegativePieceProperties
import ContinuousFlexibility.Analysis.N04bRootPastingInverse
import ContinuousFlexibility.Analysis.N04bActualRootInterior

/-!
# A genuinely constructed negative canonical piece

The local root model and its collar inverse are obtained from the raw
cumulative N03 field. Literal pasting preserves the actual interior
formulas. Continuity identifies the pasted boundary values with the
actual closed travel inverse, while the local inverse theorem gives full
inverse germs at both the physical root and the moving artificial cut.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04b_exists_actual_negative_piece
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) :
    ∃ (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ)
      (J : PolarPoint → PolarPoint),
      N04bNegativePieceProperties S C L z m side F h J := by
  let Ω := n04bActualNegativeDomain S C L z m side
  let r₀ := if side then C.right m else C.left m
  let B := n04bRootCutRadius (C.travel m)
  let e := n04bRootAffine r₀ side
  let Fraw := n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side
  let hraw := n04bRootPhysicalHeight (L.coefficients z)
    (n04bCharacteristicHalfGap (L.coefficients z))
    (n04bActualTravelChart S C L z m) (C.travel m) side
  let Jraw := n04bRootPhysicalInverse (n04bActualTravelInverse S C L z m) (C.travel m) side
  let Jclosed := n04bRootPhysicalInverse
    (n04bActualClosedTravelInverse S C L z m) (C.travel m) side
  have hTravel := n04b_actualTravel_positive hN hS hT hfield hz hs m
  have hB : 0 < B := n04bRootCutRadius_pos hTravel
  have hTravelBij := n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m
  have hX := n04b_actualTravelInverse_spec hN hS hT hfield hz hs m
  have hClosedBij := n04b_actualTravelChart_closed_bijOn hN hS hT hfield hz hs m
  have hRawData := n04b_rootPhysical_chart_data hTravel hTravelBij.mapsTo hX.1
    (fun p hp => hX.2.1 hp) (fun q hq => hX.2.2.1 hq) side
  have hRawInj : InjOn Fraw Ω := by
    intro p hp q hq he
    calc
      p = Jraw (Fraw p) := (hRawData.2.2.1 p hp).symm
      _ = Jraw (Fraw q) := congrArg Jraw he
      _ = q := hRawData.2.2.1 q hq
  obtain ⟨M⟩ := n04b_exists_actual_rootPastingModel hT hS hN hfield hz hs m side
  obtain ⟨G, hRoot, hJZero⟩ := M.exists_literal_root_germs hB hRawInj
    hRawData.2.1 (fun q hq => hRawData.2.2.2 q hq)
  let F := n04bPastedRootChart r₀ side M.rootChart Fraw
  let h := n04bPastedRootHeight r₀ side M.rootHeight hraw
  let J := n04bPastedRootInverse r₀ side G Jraw
  have hChartGerm (p : PolarPoint) (hp : 0 < (e p).1) :
      F =ᶠ[𝓝 p] Fraw :=
    n04bPastedRootChart_physical_germ r₀ side M.rootChart Fraw hp
  have hHeightGerm (p : PolarPoint) (hp : 0 < (e p).1) :
      h =ᶠ[𝓝 p] hraw :=
    n04bPastedRootHeight_physical_germ r₀ side M.rootHeight hraw hp
  have hInverseGerm (q : PolarPoint) (hq : 0 < q.1) :
      J =ᶠ[𝓝 q] Jraw :=
    n04bPastedRootInverse_physical_germ r₀ side G Jraw hq
  have hClosure : closure Ω =
      n04bTravelDomain (Icc (C.left m) (C.right m) ×ˢ univ)
        (n04bActualTravelChart S C L z m)
        (n04bClosedTravelHalfInterval (C.travel m) side) :=
    n04b_actualTravelHalf_closure hN hS hT hfield hz hs m side
  have hClass (p : PolarPoint) (hp : p ∈ closure Ω) :
      p.1 = r₀ ∨ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    apply n04b_closedTravelHalf_root_or_interior hTravel side
      (fun θ => congrArg Prod.fst
        (n04b_actualTravelChart_endpoints hN hS hT hfield hz hs m θ).1)
      (fun θ => congrArg Prod.fst
        (n04b_actualTravelChart_endpoints hN hS hT hfield hz hs m θ).2)
    rwa [← hClosure]
  have hInteriorRegular (p : PolarPoint)
      (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
      ContDiffAt ℝ ∞ F p ∧ ContDiffAt ℝ ∞ h p ∧ planeJacobian F p ≠ 0 ∧ 0 < h p := by
    have hrawReg := n04b_actualRootPhysical_regular_at hN hS hT hfield hz hs m side hp
    have hpPos := n04bRootAffine_first_pos_of_interior side hp
    have hFg := hChartGerm p hpPos
    have hHg := hHeightGerm p hpPos
    refine ⟨hrawReg.1.congr_of_eventuallyEq hFg,
      hrawReg.2.1.congr_of_eventuallyEq hHg, ?_, ?_⟩
    · have hJEq : planeJacobian F p = planeJacobian Fraw p := by
        unfold planeJacobian
        rw [hFg.fderiv_eq]
      rw [hJEq]
      exact hrawReg.2.2.1
    · rw [hHg.self_of_nhds]
      exact hrawReg.2.2.2
  have hClosedRegular (p : PolarPoint) (hp : p ∈ closure Ω) :
      ContDiffAt ℝ ∞ F p ∧ ContDiffAt ℝ ∞ h p ∧ planeJacobian F p ≠ 0 ∧ 0 < h p := by
    rcases hClass p hp with hpRoot | hpInterior
    · have he : p = (r₀, p.2) := Prod.ext hpRoot rfl
      rw [he]
      have hr := hRoot p.2
      exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩
    · exact hInteriorRegular p hpInterior
  have hInverseRegular (q : PolarPoint) (hq : q ∈ Icc (0 : ℝ) B ×ˢ (univ : Set ℝ)) :
      ContDiffAt ℝ ∞ J q := by
    by_cases hqPos : 0 < q.1
    · exact (n04b_actualRootPhysicalInverse_contDiffAt hN hS hT hfield hz hs m side
        ⟨hqPos, hq.1.2⟩).congr_of_eventuallyEq (hInverseGerm q hqPos)
    · exact hJZero q (le_antisymm (le_of_not_gt hqPos) hq.1.1)
  have hClosedSub : closure Ω ⊆ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    intro p hp
    rw [hClosure] at hp
    exact (mem_n04bTravelDomain.mp hp).1
  have hFOpenEq : EqOn F Fraw Ω := by
    intro p hp
    have hpWhole : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      (mem_n04bTravelDomain.mp hp).1
    exact (hChartGerm p (n04bRootAffine_first_pos_of_interior side hpWhole)).self_of_nhds
  have hFClosedEq : EqOn F Fraw (closure Ω) :=
    hFOpenEq.of_subset_closure
      (fun p hp => (hClosedRegular p hp).1.continuousAt.continuousWithinAt)
      ((n04b_actualRootPhysicalChart_continuousOn_closed
        hN hS hT hfield hz hs m side).mono hClosedSub)
      subset_closure (Subset.rfl)
  have hClosedOpenEq := n04b_closedRootPhysicalInverse_eq_interior
    hTravel hClosedBij hX.1 hX.2.2.1 side
  have hJOpenEq : EqOn J Jclosed (Ioo (0 : ℝ) B ×ˢ (univ : Set ℝ)) := by
    intro q hq
    exact (hInverseGerm q hq.1.1).self_of_nhds.trans (hClosedOpenEq hq).symm
  have hCanClosure : closure (Ioo (0 : ℝ) B ×ˢ (univ : Set ℝ)) =
      Icc (0 : ℝ) B ×ˢ (univ : Set ℝ) := by
    rw [closure_prod_eq, closure_Ioo hB.ne, closure_univ]
  have hJClosedEq : EqOn J Jclosed (Icc (0 : ℝ) B ×ˢ (univ : Set ℝ)) :=
    hJOpenEq.of_subset_closure
      (fun q hq => (hInverseRegular q hq).continuousAt.continuousWithinAt)
      (n04b_actualRootClosedInverse_continuousOn hN hS hT hfield hz hs m side)
      (prod_mono Ioo_subset_Icc_self (Subset.rfl))
      (by rw [hCanClosure]; exact Subset.rfl)
  refine ⟨F, h, J, {
    closed_chart_eq := hFClosedEq
    closed_inverse_eq := hJClosedEq
    chart_physical_germ := hChartGerm
    height_physical_germ := hHeightGerm
    inverse_physical_germ := hInverseGerm
    closed_regular := hClosedRegular
    inverse_regular := hInverseRegular
    boundary_inverse := ?_
  }⟩
  intro p hp
  rcases hClass p hp with hpRoot | hpInterior
  · have he : p = (r₀, p.2) := Prod.ext hpRoot rfl
    rw [he]
    exact (hRoot p.2).2.2.2.2
  · have hReg := hInteriorRegular p hpInterior
    have hpPos := n04bRootAffine_first_pos_of_interior side hpInterior
    have hImagePos : 0 < (Fraw p).1 :=
      n04bRootPhysicalChart_fst_pos
        (n04b_travelOrientation_pos_of_fullStrip side (hTravelBij.mapsTo hpInterior).1)
    exact n04b_boundaryInverseGerm_of_same_germs hReg.1 hReg.2.2.1
      (n04b_actualRootPhysical_interior_inverse_germ hN hS hT hfield hz hs m side hpInterior)
      (hChartGerm p hpPos) (hInverseGerm (Fraw p) hImagePos)

end ContinuousFlexibility.Analysis
