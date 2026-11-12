import ContinuousFlexibility.Analysis.N01ResidualCircleModel

/-!
# The return residual in the original affine state coordinates

The linear sector is translated by the actual reference state. Recentring
a sector state supplies its unique sector parameter, so the circle-valued
construction defines a map on the original state space and decodes to the
frozen returnResidualField on every admissible sector state.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01ResidualSectorCoordinatesStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def referenceStateConditions.sectorParameterOfState
    (href : referenceStateConditions D S C) (z : AnnularState S × ℝ)
    (hs : _root_.ContinuousFlexibility.Statements.stateSector S z.1) : StateDirections S × ℝ :=
  (⟨z.1 - C.referenceState, (stateSectorSubmodule S).sub_mem hs href.stateSector⟩, z.2)

theorem referenceStateConditions.lift_sectorParameterOfState
    (href : referenceStateConditions D S C) (z : AnnularState S × ℝ)
    (hs : _root_.ContinuousFlexibility.Statements.stateSector S z.1) :
    liftSectorParameter S C (href.sectorParameterOfState z hs) = z := by
  apply Prod.ext
  · change C.referenceState + (z.1 - C.referenceState) = z.1
    exact (add_comm _ _).trans (sub_add_cancel _ _)
  · rfl

theorem referenceStateConditions.sectorParameterOfState_lift
    (href : referenceStateConditions D S C) (z : StateDirections S × ℝ) :
    href.sectorParameterOfState (liftSectorParameter S C z)
      (href.liftSectorParameter_sector z) = z := by
  apply Prod.ext
  · apply Subtype.ext
    change (C.referenceState + z.1.val) - C.referenceState = z.1.val
    exact add_sub_cancel_left _ _
  · rfl

theorem referenceStateConditions.sectorParameterOfState_mem
    (href : referenceStateConditions D S C) (z : AnnularState S × ℝ)
    (hs : _root_.ContinuousFlexibility.Statements.stateSector S z.1)
    (hz : z ∈ stateNeighborhood S C base ε) :
    href.sectorParameterOfState z hs ∈ sectorNeighborhood S base ε ε := by
  constructor
  · change stateGrading S base (z.1 - C.referenceState) < ε
    exact hz.1
  · exact hz.2

def N01Properties.returnResidualCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : AnnularState S × ℝ) : CircleSpace S := by
  classical
  exact if hs : stateSector S z.1 then
    hN.sectorReturnResidualCircle hS hT (hN.2.2.1.sectorParameterOfState z hs)
  else 0

theorem N01Properties.returnResidualCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.returnResidualCircle hS hT z) m θ =
      returnResidualField S C z m θ := by
  classical
  simp only [returnResidualCircle, dif_pos hs]
  exact (hN.sectorReturnResidualCircle_decode hS hT (hN.2.2.1.sectorParameterOfState z hs)
    (hN.2.2.1.sectorParameterOfState_mem z hs hz) m θ).trans
      (congrArg (fun y : AnnularState S × ℝ => returnResidualField S C y m θ)
        (hN.2.2.1.lift_sectorParameterOfState z hs))

theorem N01Properties.returnResidualCircle_lift
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) :
    hN.returnResidualCircle hS hT (liftSectorParameter S C z) =
      hN.sectorReturnResidualCircle hS hT z := by
  classical
  simp only [returnResidualCircle, dif_pos (hN.2.2.1.liftSectorParameter_sector z)]
  exact congrArg (hN.sectorReturnResidualCircle hS hT)
    (hN.2.2.1.sectorParameterOfState_lift z)

theorem N01Properties.returnResidualField_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    CircleMember T (3 / 4 : ℝ) (returnResidualField S C z) := by
  have hd : (S.circle (3 / 4 : ℝ)).decode (hN.returnResidualCircle hS hT z) =
      returnResidualField S C z :=
    funext (fun m => funext (hN.returnResidualCircle_decode hS hT z hz hs m))
  exact (congrArg (CircleMember T (3 / 4 : ℝ)) hd).mp
    ((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 (hN.returnResidualCircle hS hT z))

end ContinuousFlexibility.Statements
