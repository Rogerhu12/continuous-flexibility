module

public import ContinuousFlexibility.Analysis.N08ExpProfile
public import ContinuousFlexibility.Analysis.N08LogProfileLift
public import ContinuousFlexibility.Analysis.N08ScalarProfileRealization
public import ContinuousFlexibility.Analysis.N08NuDerivative
public import ContinuousFlexibility.Analysis.SolveReturnEquations
public import ContinuousFlexibility.Analysis.TameLocalLinear

/-!
# The actual scalar residual on the prescribed state space

The physical logarithmic profile is exponentiated in its proved positive
weight and used in the finite scalar formula. Projection to the compatible
source space is global. On every admissible sector state it is identified
with the literal residual, including its removable value at `q = 0`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n08ProfilePerturbation
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) :
    (S.height n08WeakControlWeight).Space :=
  n08ExpProfile hT hS (n08LogProfileLift hT hS hN x)

theorem n08ProfilePerturbation_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) (p : PolarPoint) :
    (S.height n08WeakControlWeight).decode (n08ProfilePerturbation hT hS hN x) p =
      Real.exp (n08_stateLogProfile D S C x p.1) - 1 := by
  rw [n08ProfilePerturbation, n08ExpProfile_decode hT hS,
    n08LogProfileLift_decode hT hS hN]

theorem n08ProfilePerturbation_realizesProfile
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) (p : PolarPoint) :
    D.w p.1 * (1 + (S.height n08WeakControlWeight).decode
      (n08ProfilePerturbation hT hS hN x) p) = stateProfile D S C x p.1 := by
  rw [n08ProfilePerturbation_decode hT hS hN x p]
  change D.w p.1 * (1 + (Real.exp (n08_stateLogProfile D S C x p.1) - 1)) =
    D.w p.1 * Real.exp (n08_stateLogProfile D S C x p.1)
  ring

theorem n08ProfilePerturbation_reference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    n08ProfilePerturbation hT hS hN C.referenceState = 0 := by
  rw [n08ProfilePerturbation, n08LogProfileLift_reference hT hS hN, n08ExpProfile_zero hT hS]

def n08LogParameterCLM
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    AnnularState S × ℝ →L[ℝ] (S.height n08WeakControlWeight).Space :=
  (n08LogProfileLift hT hS hN).comp (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ)

theorem n08LogParameterCLM_isTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    IsTameLinear (pairGrading (stateGrading S) realGrading)
      (S.height n08WeakControlWeight).grading (n08LogParameterCLM hT hS hN).toLinearMap 0 0 :=
  inverseTame_comp_zero (n08LogProfileLift_isTame hT hS hN)
    (inverseTame_fst (stateGrading S) realGrading)

theorem n08ProfilePerturbation_parameter_uniformTameGerm
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    UniformTameGerm (pairGrading (stateGrading S) realGrading)
      (S.height n08WeakControlWeight).grading (C.referenceState, 0)
      (fun z : AnnularState S × ℝ => n08ProfilePerturbation hT hS hN z.1) := by
  have hp := tamePairGrading_monotone (solve_stateGrading_monotone S)
    weighted_realGrading_monotone
  have ht := withSeminorms_pairGrading (solve_stateGrading_withSeminorms S)
    weighted_realGrading_withSeminorms
  have hlog := uniformTameGerm_continuousLinear ht (C.referenceState, 0)
    (n08LogParameterCLM hT hS hN) (n08LogParameterCLM_isTame hT hS hN)
  have hzero : n08LogParameterCLM hT hS hN (C.referenceState, 0) = 0 :=
    n08LogProfileLift_reference hT hS hN
  exact hlog.n08ExpProfile hzero hT hS hp ht

def n08ActualScalarResidual
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) : AnnularState S × ℝ → S.Source :=
  n08ScalarSourceResidual hT hS hN n08WeakControlWeight_pos.le
    (n08ProfilePerturbation hT hS hN)

theorem n08ActualScalarResidual_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode (n08ActualScalarResidual hT hS hN z).val p =
      scalarResidualField D S C z p :=
  n08ScalarSourceResidual_decode hT hS hN n08WeakControlWeight_pos.le
    (n08ProfilePerturbation hT hS hN) hz hs
    (fun p _ => n08ProfilePerturbation_realizesProfile hT hS hN z.1 p) p hp

theorem n08ActualScalarResidual_reference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    n08ActualScalarResidual hT hS hN (C.referenceState, 0) = 0 :=
  n08_source_reference_zero hS hN.1 hN.2.2.1
    (n08ActualScalarResidual hT hS hN (C.referenceState, 0))
    (n08ActualScalarResidual_decode hT hS hN (z := (C.referenceState, 0))
      (n08_reference_mem_stateNeighborhood hN.2.1) hN.2.2.1.stateSector)

theorem n08ActualScalarResidual_uniformTameGerm
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    UniformTameGerm (pairGrading (stateGrading S) realGrading) S.sourceGrading
      (C.referenceState, 0) (n08ActualScalarResidual hT hS hN) :=
  n08ScalarSourceResidual_uniformTameGerm hT hS hN n08WeakControlWeight_pos.le
    (n08ProfilePerturbation hT hS hN) (n08ProfilePerturbation_parameter_uniformTameGerm hT hS hN)

end ContinuousFlexibility.Statements
