import ContinuousFlexibility.Analysis.N08ExtendedLogProfile
import ContinuousFlexibility.Analysis.N08ActualScalarResidual

/-!
# The actual scalar residual with an independent weak control

The extra control is inserted in the realized logarithmic profile before
exponentiation. The height variables are unchanged. Finite weighted scalar
calculus and the actual source projection give one uniform tame germ, and
physical circle controls recover exactly the original residual lines.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

def n08ExtendedHeightParameterCLM (S : PhysicalSpacesData) :
    (AnnularState S × ℝ) × ControlBanach →L[ℝ] ScalarWeightedState S :=
  (n08ScalarHeightParameter S).comp
    (ContinuousLinearMap.fst ℝ (AnnularState S × ℝ) ControlBanach)

theorem n08ExtendedHeightParameterCLM_isTame (S : PhysicalSpacesData) :
    IsTameLinear (n08ExtendedControlGrading S) (scalarStateGrading S)
      (n08ExtendedHeightParameterCLM S).toLinearMap 0 0 :=
  inverseTame_comp_zero (n08ScalarHeightParameter_isTame S)
    (inverseTame_fst (n08StateParameterGrading S) controlGrading)

theorem n08ExtendedHeightParameterCLM_uniformTameGerm (S : PhysicalSpacesData)
    (x0 : AnnularState S) :
    UniformTameGerm (n08ExtendedControlGrading S) (scalarStateGrading S)
      ((x0, 0), 0) (n08ExtendedHeightParameterCLM S) :=
  uniformTameGerm_continuousLinear (n08ExtendedControlGrading_topology S)
    ((x0, 0), 0) (n08ExtendedHeightParameterCLM S)
    (n08ExtendedHeightParameterCLM_isTame S)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n08ExtendedControlResidual
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (z : (AnnularState S × ℝ) × ControlBanach) : S.Source :=
  n08SourceProjection hS
    (n08ProfileResidual hN.1.1 hT hS n08WeakControlWeight_pos.le
      (n08ExpProfile hT hS (n08ExtendedLogProfileLift hT hS hN z))
      (n08ScalarHeightParameter S z.1))

theorem n08ExtendedControlResidual_uniformTameGerm
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    UniformTameGerm (n08ExtendedControlGrading S) S.sourceGrading
      ((C.referenceState, 0), 0) (n08ExtendedControlResidual hT hS hN) := by
  have hp := n08ExtendedControlGrading_monotone S
  have ht := n08ExtendedControlGrading_topology S
  have hm := (n08ExtendedLogProfileLift_uniformTameGerm hT hS hN).n08ExpProfile
    (n08ExtendedLogProfileLift_reference hT hS hN) hT hS hp ht
  exact n08SourceProjection_postcompose_uniformTameGerm hS hp ht
    (hm.n08ProfileResidual (n08ExtendedHeightParameterCLM_uniformTameGerm S C.referenceState)
      rfl hN.1.1 hT hS n08WeakControlWeight_pos.le hp ht)

theorem n08ExtendedControlResidual_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) :
    n08ExtendedControlResidual hT hS hN (z, 0) = n08ActualScalarResidual hT hS hN z := by
  unfold n08ExtendedControlResidual n08ActualScalarResidual n08ScalarSourceResidual
    n08ProfilePerturbation
  rw [n08ExtendedLogProfileLift_apply, map_zero, add_zero]

theorem n08ExtendedControlResidual_reference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    n08ExtendedControlResidual hT hS hN ((C.referenceState, 0), 0) = 0 := by
  rw [n08ExtendedControlResidual_zero, n08ActualScalarResidual_reference hT hS hN]

/-- This is equality of the actual source elements on the whole affine
line, not merely agreement of an encoded jet or of a sector restriction. -/
theorem n08ExtendedControlResidual_controlLine
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) (u : CircleSpace S) (t : ℝ) :
    n08ExtendedControlResidual hT hS hN (z, t • n08ControlRestriction S u) =
      n08ActualScalarResidual hT hS hN
        (z.1 + n08StateSMul S t (0, (0, (u, 0))), z.2) := by
  unfold n08ExtendedControlResidual n08ActualScalarResidual n08ScalarSourceResidual
    n08ProfilePerturbation
  rw [n08ExtendedLogProfileLift_controlLine hT hS hN,
    n08ScalarHeightParameter_controlLine]

end ContinuousFlexibility.Statements
