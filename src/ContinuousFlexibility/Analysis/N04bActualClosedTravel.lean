module

public import ContinuousFlexibility.Analysis.N04bActualTravelChart
public import ContinuousFlexibility.Analysis.N04bRootPhysicalBoundary
public import ContinuousFlexibility.Analysis.N04bRootInteriorRegularity

/-!
# The actual closed travel inverse of the cumulative N03 witness

Both endpoint circle maps are genuine bijections. Together with the
proved actual interior travel chart they construct the inverse on the
closed physical strip. Its values agree with the stored actual interior
inverse wherever the travel coordinate is interior.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

def n04bActualClosedTravelInverse (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ) (m : ℕ) :
    PolarPoint → PolarPoint :=
  Function.invFunOn (n04bActualTravelChart S C L z m)
    (Icc (C.left m) (C.right m) ×ˢ univ)

section Actual

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ)

include hN hS hz hs in
theorem n04b_actualTravel_endpoint_bijections :
    Function.Bijective (stateLeftChart S z.1 m) ∧
      Function.Bijective (rightChartCandidate S C z m) := by
  have hleft := hN.1.1.2.2.2.2.2.2.2.1 z hz hs m
  have hLeftPos : ∀ θ, 0 < deriv (stateLeftChart S z.1 m) θ :=
    fun θ => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hleft θ).1
  refine ⟨⟨(strictMono_of_deriv_pos hLeftPos).injective,
    surjective_of_continuous_periodic_lift Real.pi_ne_zero
      (stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))).continuous
      (fun θ => (hleft θ).2.2.1)⟩, ?_⟩
  refine ⟨(strictMono_of_deriv_pos
    (N01Properties.rightChart_deriv_pos S C z m hN.1.1 hz hs)).injective, ?_⟩
  intro θ
  exact ⟨C.rightChartInverse z m θ,
    (N01Properties.return_inverse_and_positive S C z m hN.1.1 hz hs θ).2.2.1⟩

include hN hS hT hfield hz hs in
theorem n04b_actualTravelChart_closed_bijOn :
    BijOn (n04bActualTravelChart S C L z m)
      (Icc (C.left m) (C.right m) ×ˢ univ)
      (Icc (0 : ℝ) (C.travel m) ×ˢ univ) := by
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hb := n04b_actualTravel_endpoint_bijections hN hS hz hs m
  exact n04b_closedTravelStrip_bijOn (hcontrol.1 m).2.1
    (n04b_actualTravel_positive hN hS hT hfield hz hs m)
    (n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m)
    (fun θ => (n04b_actualTravelChart_endpoints hN hS hT hfield hz hs m θ).1)
    (fun θ => (n04b_actualTravelChart_endpoints hN hS hT hfield hz hs m θ).2)
    hb.1 hb.2

include hN hS hT hfield hz hs in
theorem n04b_actualClosedTravelInverse_spec :
    MapsTo (n04bActualClosedTravelInverse S C L z m)
        (Icc (0 : ℝ) (C.travel m) ×ˢ univ)
        (Icc (C.left m) (C.right m) ×ˢ univ) ∧
      LeftInvOn (n04bActualClosedTravelInverse S C L z m)
        (n04bActualTravelChart S C L z m) (Icc (C.left m) (C.right m) ×ˢ univ) ∧
      RightInvOn (n04bActualClosedTravelInverse S C L z m)
        (n04bActualTravelChart S C L z m) (Icc (0 : ℝ) (C.travel m) ×ˢ univ) ∧
      ContinuousOn (n04bActualClosedTravelInverse S C L z m)
        (Icc (0 : ℝ) (C.travel m) ×ˢ univ) ∧
      EqOn (n04bActualClosedTravelInverse S C L z m)
        (n04bActualTravelInverse S C L z m) (Ioo (0 : ℝ) (C.travel m) ×ˢ univ) := by
  have hBij := n04b_actualTravelChart_closed_bijOn hN hS hT hfield hz hs m
  have hOpen := n04b_actualTravelInverse_spec hN hS hT hfield hz hs m
  refine ⟨hBij.surjOn.mapsTo_invFunOn, hBij.injOn.leftInvOn_invFunOn,
    hBij.surjOn.rightInvOn_invFunOn, ?_, ?_⟩
  · apply n04b_closedTravelInverse_continuous Real.pi_ne_zero
      (n04b_actualTravelChart_continuous hN hS hT hfield hz hs m) hBij
    intro r hr θ
    simpa only [Prod.snd_add] using congrArg Prod.snd
      (n04b_actualTravelChart_period_add hN hS hT hfield hz hs m hr θ)
  · exact n04b_closedTravelInverse_eq_interior hBij hOpen.1 hOpen.2.2.1

include hN hS hT hfield hz hs in
theorem n04b_actualTravelHalf_closure (side : Bool) :
    closure (n04bTravelHalfDomain
      (Ioo (C.left m) (C.right m) ×ˢ univ)
      (n04bActualTravelChart S C L z m) (C.travel m) side) =
      n04bTravelDomain (Icc (C.left m) (C.right m) ×ˢ univ)
        (n04bActualTravelChart S C L z m)
        (n04bClosedTravelHalfInterval (C.travel m) side) := by
  apply n04b_closure_travelHalf
    (n04b_actualTravel_positive hN hS hT hfield hz hs m) Real.pi_ne_zero
    (n04b_actualTravelChart_continuous hN hS hT hfield hz hs m)
    (n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m)
    (n04b_actualTravelChart_closed_bijOn hN hS hT hfield hz hs m)
  intro r hr θ
  simpa only [Prod.snd_add] using congrArg Prod.snd
    (n04b_actualTravelChart_period_add hN hS hT hfield hz hs m hr θ)

include hN hS hT hfield hz hs in
theorem n04b_actualClosedTravelInverse_endpoint_images (side : Bool) :
    n04bActualClosedTravelInverse S C L z m ''
        ({if side then C.travel m else 0} ×ˢ (univ : Set ℝ)) =
      ({if side then C.right m else C.left m} ×ˢ (univ : Set ℝ)) := by
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hab := (hcontrol.1 m).2.1.le
  have hBij := n04b_actualTravelChart_closed_bijOn hN hS hT hfield hz hs m
  have hb := n04b_actualTravel_endpoint_bijections hN hS hz hs m
  cases side with
  | false =>
    exact n04b_closedTravelInverse_image_endpoint hBij (left_mem_Icc.mpr hab)
      (fun θ => (n04b_actualTravelChart_endpoints hN hS hT hfield hz hs m θ).1) hb.1
  | true =>
    exact n04b_closedTravelInverse_image_endpoint hBij (right_mem_Icc.mpr hab)
      (fun θ => (n04b_actualTravelChart_endpoints hN hS hT hfield hz hs m θ).2) hb.2

end Actual
end ContinuousFlexibility.Analysis
