import ContinuousFlexibility.Scalar.WeightedHeightAlgebra
import ContinuousFlexibility.Scalar.WeightedStatePrimitives
import ContinuousFlexibility.Scalar.WeightedProductTower
import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-!
# Uniform tame germs of the concrete scalar height operations

The original weighted model is complete because its prescribed weak graph
is closed. This supplies the completeness used in the genuine composition
theorem, without placing an extra hypothesis on the scalar data.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

section GeneralSource

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X}
  {f g : X → ScalarHeightSpace S}

theorem UniformTameGerm.scalarHeightMul
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hg : UniformTameGerm p (scalarHeightGrading S) x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarHeightMul hT hS (f x) (g x)) := by
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  obtain ⟨base, loss, _, hB⟩ := SobolevModelData.decodedProductMap_twoFactor
    hT (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos.le
  exact hf.bilinear hg
    (SobolevModelData.decodedProductMap hT (hS.1 scalarBeta)
      (scalarHeightInterpolation hS) scalarBeta_pos.le 1)
    hB hp ht (scalarHeightGrading_monotone S) (weighted_scalarHeightGrading_withSeminorms S)

theorem UniformTameGerm.scalarHeightUnitalMul
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hg : UniformTameGerm p (scalarHeightGrading S) x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarHeightUnitalMul hT hS (f x) (g x)) :=
  (hf.add hg hp ht).add (hf.scalarHeightMul hg hT hS hp ht) hp ht

theorem UniformTameGerm.scalarHeightUnitalAct
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hg : UniformTameGerm p (scalarHeightGrading S) x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarHeightUnitalAct hT hS (f x) (g x)) :=
  hg.add (hf.scalarHeightMul hg hT hS hp ht) hp ht

theorem UniformTameGerm.scalarHeightSMul {a : X → ℝ}
    (ha : UniformTameGerm p realGrading x0 a)
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0 (fun x => a x • f x) := by
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  exact ha.smul hf hp ht (scalarHeightGrading_monotone S)
    (weighted_scalarHeightGrading_withSeminorms S)

theorem UniformTameGerm.scalarReferenceW
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarReferenceWCLM hD hT hS (f x)) :=
  hf.postcompose hp ht (scalarReferenceWCLM hD hT hS)
    (scalarReferenceWCLM_isTame hD hT hS)

theorem UniformTameGerm.scalarReferenceWDeriv
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarReferenceWDerivCLM hD hT hS (f x)) :=
  hf.postcompose hp ht (scalarReferenceWDerivCLM hD hT hS)
    (scalarReferenceWDerivCLM_isTame hD hT hS)

theorem UniformTameGerm.scalarReferenceInvW
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarReferenceInvWCLM hD hT hS (f x)) :=
  hf.postcompose hp ht (scalarReferenceInvWCLM hD hT hS)
    (scalarReferenceInvWCLM_isTame hD hT hS)

theorem UniformTameGerm.scalarReferenceRadius
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarReferenceRadiusCLM hD hT hS (f x)) :=
  hf.postcompose hp ht (scalarReferenceRadiusCLM hD hT hS)
    (scalarReferenceRadiusCLM_isTame hD hT hS)

theorem UniformTameGerm.scalarReferenceInvRadius
    (hf : UniformTameGerm p (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarReferenceInvRadiusCLM hD hT hS (f x)) :=
  hf.postcompose hp ht (scalarReferenceInvRadiusCLM hD hT hS)
    (scalarReferenceInvRadiusCLM_isTame hD hT hS)

end GeneralSource

theorem scalarStateMeanCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateMeanCLM hD hT hS) :=
  uniformTameGerm_continuousLinear (weighted_scalarStateGrading_withSeminorms S) x0
    (scalarStateMeanCLM hD hT hS) (scalarStateMeanCLM_isTame hD hT hS)

theorem scalarStateRadialCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateRadialCLM hD hT hS) :=
  uniformTameGerm_continuousLinear (weighted_scalarStateGrading_withSeminorms S) x0
    (scalarStateRadialCLM hD hT hS) (scalarStateRadialCLM_isTame hD hT hS)

theorem scalarStateRadialSecondCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateRadialSecondCLM hD hT hS) :=
  uniformTameGerm_continuousLinear (weighted_scalarStateGrading_withSeminorms S) x0
    (scalarStateRadialSecondCLM hD hT hS) (scalarStateRadialSecondCLM_isTame hD hT hS)

theorem scalarStateAngularPrimitiveCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateAngularPrimitiveCLM hD hT hS) :=
  uniformTameGerm_continuousLinear (weighted_scalarStateGrading_withSeminorms S) x0
    (scalarStateAngularPrimitiveCLM hD hT hS) (scalarStateAngularPrimitiveCLM_isTame hD hT hS)

theorem scalarStateAngularRadialPrimitiveCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateAngularRadialPrimitiveCLM hD hT hS) :=
  uniformTameGerm_continuousLinear (weighted_scalarStateGrading_withSeminorms S) x0
    (scalarStateAngularRadialPrimitiveCLM hD hT hS) (scalarStateAngularRadialPrimitiveCLM_isTame hD hT hS)

theorem scalarStateAngularSecondCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateAngularSecondCLM hD hT hS) :=
  uniformTameGerm_continuousLinear (weighted_scalarStateGrading_withSeminorms S) x0
    (scalarStateAngularSecondCLM hD hT hS) (scalarStateAngularSecondCLM_isTame hD hT hS)

theorem scalarStateMeanDerivCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateMeanDerivCLM hD hT hS) :=
  uniformTameGerm_continuousLinear (weighted_scalarStateGrading_withSeminorms S) x0
    (scalarStateMeanDerivCLM hD hT hS) (scalarStateMeanDerivCLM_isTame hD hT hS)

theorem scalarStateQProjection_uniformTameGerm (S : PhysicalSpacesData)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) realGrading x0 (scalarStateQProjection S) :=
  uniformTameGerm_continuousLinear (weighted_scalarStateGrading_withSeminorms S) x0
    (scalarStateQProjection S) (scalarStateQProjection_isTame S)

end ContinuousFlexibility.Statements
