module

public import ContinuousFlexibility.Analysis.CoupledWeakHeightCalculus
public import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear

/-!
# The actual common height jets at the weak profile weight

The radial derivative retains the endpoint constant through its cutoff.
The angular second derivative uses the same physical height and vanishes
on that radial constant. Weight shifting changes only the model, not the
decoded fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem coupledWeakProfileWeight_le_beta : coupledWeakProfileWeight ≤ scalarBeta := by
  norm_num [coupledWeakProfileWeight, scalarBeta]

def coupledHeightToWeakCLM (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarHeightSpace S →L[ℝ] CoupledWeakHeight S :=
  SobolevModelData.weightShift hT (hS.1 scalarBeta) (hS.1 coupledWeakProfileWeight)
    coupledWeakProfileWeight_le_beta

theorem coupledHeightToWeakCLM_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledHeightToWeakCLM hT hS u) p =
      (S.height scalarBeta).decode u p :=
  congrFun (SobolevModelData.decode_weightShift hT (hS.1 scalarBeta)
    (hS.1 coupledWeakProfileWeight) coupledWeakProfileWeight_le_beta u) p

theorem coupledHeightToWeakCLM_isTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarHeightGrading S) (coupledWeakHeightGrading S)
      (coupledHeightToWeakCLM hT hS).toLinearMap 0 0 :=
  SobolevModelData.weightShift_isTame hT (hS.1 scalarBeta)
    (hS.1 coupledWeakProfileWeight) coupledWeakProfileWeight_le_beta

def coupledWeakCommonRadialCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    HeightPair S →L[ℝ] CoupledWeakHeight S :=
  (coupledHeightToWeakCLM hT hS).comp (scalarCommonRadialCLM hD hT hS)

theorem coupledWeakCommonRadialCLM_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : HeightPair S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakCommonRadialCLM hD hT hS u) p =
      radialPartial (heightPairField S u) p :=
  (coupledHeightToWeakCLM_decode hT hS (scalarCommonRadialCLM hD hT hS u) p).trans
    (congrFun (decode_scalarCommonRadialCLM hD hT hS u) p)

theorem coupledWeakCommonRadialCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (heightPairGrading S) (coupledWeakHeightGrading S)
      (coupledWeakCommonRadialCLM hD hT hS).toLinearMap 2 0 :=
  (coupledHeightToWeakCLM_isTame hT hS).comp (scalarCommonRadialCLM_isTame hD hT hS)

def coupledWeakCommonAngularCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    HeightPair S →L[ℝ] CoupledWeakHeight S :=
  (coupledHeightToWeakCLM hT hS).comp
    ((scalarStateAngularSecondCLM hD hT hS).comp (scalarCommonDirectionCLM S))

theorem coupledWeakCommonAngularCLM_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : HeightPair S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakCommonAngularCLM hD hT hS u) p =
      angularPartial (heightAngular (heightPairField S u)) p :=
  (coupledHeightToWeakCLM_decode hT hS
    (scalarStateAngularSecondCLM hD hT hS (scalarCommonDirectionCLM S u)) p).trans
      (congrFun (decode_scalarStateAngularSecondCLM hD hT hS
        (scalarCommonDirectionCLM S u)) p)

theorem coupledWeakCommonAngularCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (heightPairGrading S) (coupledWeakHeightGrading S)
      (coupledWeakCommonAngularCLM hD hT hS).toLinearMap 3 0 :=
  (coupledHeightToWeakCLM_isTame hT hS).comp
    ((scalarStateAngularSecondCLM_isTame hD hT hS).comp (scalarCommonDirectionCLM_isTame S))

end ContinuousFlexibility.Statements
