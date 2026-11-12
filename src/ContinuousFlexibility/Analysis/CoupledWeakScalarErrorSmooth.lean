import ContinuousFlexibility.Analysis.CoupledWeakScalarError
import ContinuousFlexibility.Analysis.SolveTameSubspace
import ContinuousFlexibility.Scalar.WeightedHeightSmooth

/-!
# Joint smooth tame evaluation of the weak-coefficient scalar error

The independent source and height directions retain their full spaces.
Only the coefficient family has to lie in the common parameter domain.
The actual conservation law restricts every derivative in the genuine
tower to the original Source subspace.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {U : Set X}
  {t : X → CoupledWeakHeight S} {R : X → ScalarHeightSpace S} {u : X → HeightPair S}

theorem coupledWeakTypeMultiplierCLM_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (htype : SmoothTameOn p (coupledWeakHeightGrading S) U t)
    (hR : SmoothTameOn p (scalarHeightGrading S) U R) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => coupledWeakTypeMultiplierCLM hD hT hS (t x) (R x)) := by
  have href := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) hR
    (scalarReferenceTypeCLM hD hT hS) (scalarReferenceTypeCLM_isTame hD hT hS)
  have hm := htype.coupledMixedWeightAction hR hT hS coupledWeakProfileWeight_pos.le hp ht
  have hmain := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) (smoothTameOn_add hp href hm)
    (scalarReferenceInvWCLM hD hT hS) (scalarReferenceInvWCLM_isTame hD hT hS)
  exact smoothTameOn_congr hmain
    (fun x _ => (coupledWeakTypeMultiplierCLM_apply hD hT hS (t x) (R x)).symm)

theorem coupledWeakTypeErrorLinear_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (htype : SmoothTameOn p (coupledWeakHeightGrading S) U t)
    (hR : SmoothTameOn p (scalarHeightGrading S) U R)
    (hu : SmoothTameOn p (heightPairGrading S) U u) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => coupledWeakTypeErrorLinear hD hT hS (t x) (R x) (u x)) := by
  have hm := coupledWeakTypeMultiplierCLM_smoothTameOn hD hT hS hp ht htype hR
  have hup := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarCommonHeightGrading_withSeminorms S) hu
    (scalarCommonProjectionCLM S) (scalarCommonProjectionCLM_isTame S)
  have ho := smoothTameOn_scalarHeightOddMul hT hS hp ht hm hup
  have hmain := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) ho
    (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta))
    (SobolevModelData.angularSecondCLM_isTame hT (hS.1 scalarBeta))
  exact smoothTameOn_congr hmain (fun x _ =>
    ((coupledWeakTypeErrorLinear_apply hD hT hS (t x) (R x) (u x)).trans
      (coupledWeakTypeErrorCLM_apply hD hT hS (t x) (R x) (u x))).symm)

/-- The joint tower has Source values, including all independent argument
directions; no coefficient membership or compatibility hypothesis is added. -/
theorem coupledWeakTypeErrorSourceLinear_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (htype : SmoothTameOn p (coupledWeakHeightGrading S) U t)
    (hR : SmoothTameOn p (scalarHeightGrading S) U R)
    (hu : SmoothTameOn p (heightPairGrading S) U u) :
    SmoothTameOn p S.sourceGrading U
      (fun x => coupledWeakTypeErrorSourceLinear hD hT hS (t x) (R x) (u x)) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  exact solve_smoothTameOn_codRestrict S.Q.toLinearMap.ker S.Q.isClosed_ker
    (coupledWeakTypeErrorLinear_smoothTameOn hD hT hS hp ht htype hR hu)
    (fun x => coupledWeakTypeErrorSourceLinear hD hT hS (t x) (R x) (u x))
    (fun x _ => coupledWeakTypeErrorSourceLinear_val hD hT hS (t x) (R x) (u x))

end ContinuousFlexibility.Statements
