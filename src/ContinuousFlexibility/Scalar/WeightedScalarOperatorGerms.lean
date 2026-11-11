import ContinuousFlexibility.Scalar.WeightedScalarError
import ContinuousFlexibility.Scalar.WeightedOddHeightGerms

/-!
# Uniform tame germs of the actual operator and correction error

All operations below are the previously constructed continuous linear or
bilinear maps. Their genuine towers compose on one common source
neighborhood with one fixed base and loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X}
  {a b c t R : X → ScalarHeightSpace S} {u : X → ScalarCommonHeight S}

theorem scalarCoefficientNormalCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (ha : UniformTameGerm p (scalarHeightGrading S) x0 a)
    (hb : UniformTameGerm p (scalarHeightGrading S) x0 b)
    (hu : UniformTameGerm p (scalarCommonHeightGrading S) x0 u) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarCoefficientNormalCLM hD hT hS (a x) (b x) (u x)) := by
  have hur := hu.postcompose hp ht (scalarCommonRadialCLM hD hT hS)
    (scalarCommonRadialCLM_isTame hD hT hS)
  have hup := hu.postcompose hp ht (scalarCommonProjectionCLM S)
    (scalarCommonProjectionCLM_isTame S)
  have hmain := ((hur.scalarReferenceW hD hT hS hp ht).add
    (ha.scalarHeightMul hur hT hS hp ht) hp ht).add
      (hb.scalarHeightAngularMul hup hT hS hp ht) hp ht
  apply hmain.congr
  intro x
  rw [scalarCoefficientNormalCLM_apply] <;> rfl

theorem scalarCoefficientAngularPrimitiveCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (hb : UniformTameGerm p (scalarHeightGrading S) x0 b)
    (hc : UniformTameGerm p (scalarHeightGrading S) x0 c)
    (hu : UniformTameGerm p (scalarCommonHeightGrading S) x0 u) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarCoefficientAngularPrimitiveCLM hD hT hS (b x) (c x) (u x)) := by
  have hur := hu.postcompose hp ht (scalarCommonRadialCLM hD hT hS)
    (scalarCommonRadialCLM_isTame hD hT hS)
  have hup := hu.postcompose hp ht (scalarCommonProjectionCLM S)
    (scalarCommonProjectionCLM_isTame S)
  have href := hup.postcompose hp ht (scalarReferenceCorrectedCLM hD hT hS)
    (scalarReferenceCorrectedCLM_isTame hD hT hS)
  have hmain := ((hur.scalarHeightOddMul hb hT hS hp ht).add
    (hc.scalarHeightOddMul hup hT hS hp ht) hp ht).add href hp ht
  apply hmain.congr
  intro x
  rw [scalarCoefficientAngularPrimitiveCLM_apply] <;> rfl

/-- The full corrected divergence preserves uniform tame germs. -/
theorem scalarCoefficientOperatorCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (ha : UniformTameGerm p (scalarHeightGrading S) x0 a)
    (hb : UniformTameGerm p (scalarHeightGrading S) x0 b)
    (hc : UniformTameGerm p (scalarHeightGrading S) x0 c)
    (hu : UniformTameGerm p (scalarCommonHeightGrading S) x0 u) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarCoefficientOperatorCLM hD hT hS (a x) (b x) (c x) (u x)) := by
  have hn := scalarCoefficientNormalCLM_uniformTameGerm hD hT hS hp ht ha hb hu
  have ha := scalarCoefficientAngularPrimitiveCLM_uniformTameGerm hD hT hS hp ht hb hc hu
  have hmain := (hn.postcompose hp ht (SobolevModelData.radialCLM hT (hS.1 scalarBeta))
    (SobolevModelData.radialCLM_isTame hT (hS.1 scalarBeta))).add
      (ha.postcompose hp ht (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta))
        (SobolevModelData.angularSecondCLM_isTame hT (hS.1 scalarBeta))) hp ht
  exact hmain.congr (fun x =>
    (scalarCoefficientOperatorCLM_apply hD hT hS (a x) (b x) (c x) (u x)).symm)

theorem scalarTypeMultiplierCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (htype : UniformTameGerm p (scalarHeightGrading S) x0 t)
    (hR : UniformTameGerm p (scalarHeightGrading S) x0 R) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarTypeMultiplierCLM hD hT hS (t x) (R x)) := by
  have href := hR.postcompose hp ht (scalarReferenceTypeCLM hD hT hS)
    (scalarReferenceTypeCLM_isTame hD hT hS)
  have hmain := (href.add (htype.scalarHeightMul hR hT hS hp ht) hp ht).scalarReferenceInvW
    hD hT hS hp ht
  exact hmain.congr (fun x => (scalarTypeMultiplierCLM_apply hD hT hS (t x) (R x)).symm)

/-- The actual error CLM is composed before exposing the curried linear family. -/
theorem scalarTypeErrorCLM_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (htype : UniformTameGerm p (scalarHeightGrading S) x0 t)
    (hR : UniformTameGerm p (scalarHeightGrading S) x0 R)
    (hu : UniformTameGerm p (scalarCommonHeightGrading S) x0 u) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarTypeErrorCLM hD hT hS (t x) (R x) (u x)) := by
  have hm := scalarTypeMultiplierCLM_uniformTameGerm hD hT hS hp ht htype hR
  have hup := hu.postcompose hp ht (scalarCommonProjectionCLM S)
    (scalarCommonProjectionCLM_isTame S)
  have hmain := (hm.scalarHeightOddMul hup hT hS hp ht).postcompose hp ht
    (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta))
    (SobolevModelData.angularSecondCLM_isTame hT (hS.1 scalarBeta))
  exact hmain.congr
    (fun x => (scalarTypeErrorCLM_apply hD hT hS (t x) (R x) (u x)).symm)

/-- The correction error has a genuine joint uniform tower in the state,
source height and common height arguments. -/
theorem scalarTypeErrorLinear_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (htype : UniformTameGerm p (scalarHeightGrading S) x0 t)
    (hR : UniformTameGerm p (scalarHeightGrading S) x0 R)
    (hu : UniformTameGerm p (scalarCommonHeightGrading S) x0 u) :
    UniformTameGerm p (scalarHeightGrading S) x0
      (fun x => scalarTypeErrorLinear hD hT hS (t x) (R x) (u x)) := by
  exact UniformTameGerm.congr
    (f := fun x => scalarTypeErrorCLM hD hT hS (t x) (R x) (u x))
    (g := fun x => scalarTypeErrorLinear hD hT hS (t x) (R x) (u x))
    (scalarTypeErrorCLM_uniformTameGerm hD hT hS hp ht htype hR hu)
    (fun x => (scalarTypeErrorLinear_apply hD hT hS (t x) (R x) (u x)).symm)

end ContinuousFlexibility.Statements
