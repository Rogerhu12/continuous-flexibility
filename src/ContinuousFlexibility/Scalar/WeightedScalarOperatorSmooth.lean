import ContinuousFlexibility.Scalar.WeightedScalarError
import ContinuousFlexibility.Scalar.WeightedHeightSmooth

/-!
# Smooth tame operator evaluation on full parameter domains

The state-dependent coefficient heights and each independent height
argument are combined by their actual linear and bilinear maps. All
compositions retain the given source domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {U : Set X}
  {a b c t R : X → ScalarHeightSpace S} {u : X → ScalarCommonHeight S}

theorem scalarCoefficientNormalCLM_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (ha : SmoothTameOn p (scalarHeightGrading S) U a)
    (hb : SmoothTameOn p (scalarHeightGrading S) U b)
    (hu : SmoothTameOn p (scalarCommonHeightGrading S) U u) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => scalarCoefficientNormalCLM hD hT hS (a x) (b x) (u x)) := by
  have hur := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarCommonHeightGrading_withSeminorms S) hu
    (scalarCommonRadialCLM hD hT hS) (scalarCommonRadialCLM_isTame hD hT hS)
  have hup := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarCommonHeightGrading_withSeminorms S) hu
    (scalarCommonProjectionCLM S) (scalarCommonProjectionCLM_isTame S)
  have href := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) hur
    (scalarReferenceWCLM hD hT hS) (scalarReferenceWCLM_isTame hD hT hS)
  have hm := smoothTameOn_scalarHeightMul hT hS hp ht ha hur
  have ho := smoothTameOn_scalarHeightAngularMul hT hS hp ht hb hup
  apply smoothTameOn_congr (smoothTameOn_add hp (smoothTameOn_add hp href hm) ho)
  intro x _
  rw [scalarCoefficientNormalCLM_apply] <;> rfl

theorem scalarCoefficientAngularPrimitiveCLM_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (hb : SmoothTameOn p (scalarHeightGrading S) U b)
    (hc : SmoothTameOn p (scalarHeightGrading S) U c)
    (hu : SmoothTameOn p (scalarCommonHeightGrading S) U u) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => scalarCoefficientAngularPrimitiveCLM hD hT hS (b x) (c x) (u x)) := by
  have hur := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarCommonHeightGrading_withSeminorms S) hu
    (scalarCommonRadialCLM hD hT hS) (scalarCommonRadialCLM_isTame hD hT hS)
  have hup := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarCommonHeightGrading_withSeminorms S) hu
    (scalarCommonProjectionCLM S) (scalarCommonProjectionCLM_isTame S)
  have href := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) hup
    (scalarReferenceCorrectedCLM hD hT hS) (scalarReferenceCorrectedCLM_isTame hD hT hS)
  have hbpart := smoothTameOn_scalarHeightOddMul hT hS hp ht hur hb
  have hcpart := smoothTameOn_scalarHeightOddMul hT hS hp ht hc hup
  apply smoothTameOn_congr (smoothTameOn_add hp (smoothTameOn_add hp hbpart hcpart) href)
  intro x _
  rw [scalarCoefficientAngularPrimitiveCLM_apply] <;> rfl

/-- Smooth tame evaluation on the entire given joint parameter domain. -/
theorem scalarCoefficientOperatorCLM_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (ha : SmoothTameOn p (scalarHeightGrading S) U a)
    (hb : SmoothTameOn p (scalarHeightGrading S) U b)
    (hc : SmoothTameOn p (scalarHeightGrading S) U c)
    (hu : SmoothTameOn p (scalarCommonHeightGrading S) U u) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => scalarCoefficientOperatorCLM hD hT hS (a x) (b x) (c x) (u x)) := by
  have hn := scalarCoefficientNormalCLM_smoothTameOn hD hT hS hp ht ha hb hu
  have ha := scalarCoefficientAngularPrimitiveCLM_smoothTameOn hD hT hS hp ht hb hc hu
  have hr := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) hn
    (SobolevModelData.radialCLM hT (hS.1 scalarBeta))
    (SobolevModelData.radialCLM_isTame hT (hS.1 scalarBeta))
  have ht' := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) ha
    (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta))
    (SobolevModelData.angularSecondCLM_isTame hT (hS.1 scalarBeta))
  exact smoothTameOn_congr (smoothTameOn_add hp hr ht')
    (fun x _ => (scalarCoefficientOperatorCLM_apply hD hT hS (a x) (b x) (c x) (u x)).symm)

theorem scalarTypeMultiplierCLM_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (htype : SmoothTameOn p (scalarHeightGrading S) U t)
    (hR : SmoothTameOn p (scalarHeightGrading S) U R) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => scalarTypeMultiplierCLM hD hT hS (t x) (R x)) := by
  have href := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) hR
    (scalarReferenceTypeCLM hD hT hS) (scalarReferenceTypeCLM_isTame hD hT hS)
  have hm := smoothTameOn_scalarHeightMul hT hS hp ht htype hR
  have hmain := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) (smoothTameOn_add hp href hm)
    (scalarReferenceInvWCLM hD hT hS) (scalarReferenceInvWCLM_isTame hD hT hS)
  exact smoothTameOn_congr hmain
    (fun x _ => (scalarTypeMultiplierCLM_apply hD hT hS (t x) (R x)).symm)

theorem scalarTypeErrorLinear_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (htype : SmoothTameOn p (scalarHeightGrading S) U t)
    (hR : SmoothTameOn p (scalarHeightGrading S) U R)
    (hu : SmoothTameOn p (scalarCommonHeightGrading S) U u) :
    SmoothTameOn p (scalarHeightGrading S) U
      (fun x => scalarTypeErrorLinear hD hT hS (t x) (R x) (u x)) := by
  have hm := scalarTypeMultiplierCLM_smoothTameOn hD hT hS hp ht htype hR
  have hup := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarCommonHeightGrading_withSeminorms S) hu
    (scalarCommonProjectionCLM S) (scalarCommonProjectionCLM_isTame S)
  have ho := smoothTameOn_scalarHeightOddMul hT hS hp ht hm hup
  have hmain := smoothTameOn_scalarHeight_postcompose hS hp ht
    (weighted_scalarHeightGrading_withSeminorms S) ho
    (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta))
    (SobolevModelData.angularSecondCLM_isTame hT (hS.1 scalarBeta))
  apply smoothTameOn_congr hmain
  intro x _
  rw [scalarTypeErrorLinear_apply, scalarTypeErrorCLM_apply] <;> rfl

end ContinuousFlexibility.Statements
