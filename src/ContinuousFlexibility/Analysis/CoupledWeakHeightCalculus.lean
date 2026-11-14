module

public import ContinuousFlexibility.Analysis.CoupledLogProfileLift
public import ContinuousFlexibility.Scalar.WeightedHeightGerms
public import ContinuousFlexibility.Scalar.WeightedCompositionGerm
public import ContinuousFlexibility.Scalar.WeightedPowerExtension
public import ContinuousFlexibility.Scalar.WeightedWeightShift
public import ContinuousFlexibility.Scalar.WeightedCommonHeightCalculus

/-!
# Actual algebra at the weak positive profile weight

Products, smooth scalar functions, and the reference radial coefficients
act in the same original physical model. Strong height derivatives enter
through the canonical weight shift, with their actual decoded values.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

abbrev CoupledWeakHeight (S : PhysicalSpacesData) := (S.height coupledWeakProfileWeight).Space

def coupledWeakHeightGrading (S : PhysicalSpacesData) : ℕ → Seminorm ℝ (CoupledWeakHeight S) :=
  (S.height coupledWeakProfileWeight).grading

theorem coupledWeakHeightGrading_monotone (S : PhysicalSpacesData) :
    Monotone (coupledWeakHeightGrading S) := gradedSeminorm_monotone _ _

theorem coupledWeakHeightGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (coupledWeakHeightGrading S) := withSeminorms_graded _ _

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem coupledWeakHeightInterpolation (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (coupledWeakHeightGrading S) := (hS.2.2.2.1 coupledWeakProfileWeight).2.2

def coupledWeakHeightMul (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : CoupledWeakHeight S) : CoupledWeakHeight S :=
  SobolevModelData.decodedProductMap hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakHeightInterpolation hS) coupledWeakProfileWeight_pos.le 1 ![u, v]

theorem decode_coupledWeakHeightMul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : CoupledWeakHeight S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakHeightMul hT hS u v) p =
      (S.height coupledWeakProfileWeight).decode u p * (S.height coupledWeakProfileWeight).decode v p :=
  congrFun (SobolevModelData.decode_decodedProductMap_two hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakHeightInterpolation hS) coupledWeakProfileWeight_pos.le ![u, v]) p

/-- The decaying part of the product of two fields with background one. -/
def coupledWeakHeightUnitalMul (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : CoupledWeakHeight S) : CoupledWeakHeight S :=
  u + v + coupledWeakHeightMul hT hS u v

/-- Multiplication of a decaying height by a field with background one. -/
def coupledWeakHeightUnitalAct (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : CoupledWeakHeight S) : CoupledWeakHeight S :=
  v + coupledWeakHeightMul hT hS u v

theorem decode_coupledWeakHeightUnitalMul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : CoupledWeakHeight S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakHeightUnitalMul hT hS u v) p =
      (1 + (S.height coupledWeakProfileWeight).decode u p) *
        (1 + (S.height coupledWeakProfileWeight).decode v p) - 1 := by
  simp only [coupledWeakHeightUnitalMul, map_add, Pi.add_apply, decode_coupledWeakHeightMul]
  ring

theorem decode_coupledWeakHeightUnitalAct
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : CoupledWeakHeight S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakHeightUnitalAct hT hS u v) p =
      (1 + (S.height coupledWeakProfileWeight).decode u p) * (S.height coupledWeakProfileWeight).decode v p := by
  simp only [coupledWeakHeightUnitalAct, map_add, Pi.add_apply, decode_coupledWeakHeightMul]
  ring

theorem coupledWeakHeightMul_zero_left
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (u : CoupledWeakHeight S) :
    coupledWeakHeightMul hT hS 0 u = 0 := by
  apply (hS.1 coupledWeakProfileWeight).2.2.2.2.2.1
  funext p
  simp only [decode_coupledWeakHeightMul, map_zero, Pi.zero_apply, zero_mul]

theorem coupledWeakHeightMul_zero_right
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (u : CoupledWeakHeight S) :
    coupledWeakHeightMul hT hS u 0 = 0 := by
  apply (hS.1 coupledWeakProfileWeight).2.2.2.2.2.1
  funext p
  simp only [decode_coupledWeakHeightMul, map_zero, Pi.zero_apply, mul_zero]

private theorem coupledWeakReference_smooth (hD : IsAccumulatingProfile D) :
    ContDiff ℝ ∞ D.w := by
  obtain ⟨B, hB⟩ := hD
  exact hB.1.2.2.1.1

private theorem coupledWeakReference_positive (hD : IsAccumulatingProfile D) :
    ∀ r ∈ Ioo D.a D.b, 0 < D.w r := by
  obtain ⟨B, hB⟩ := hD
  exact hB.1.2.2.2.2.1

private theorem coupledWeakReference_left_positive (hD : IsAccumulatingProfile D) : 0 < D.a := by
  obtain ⟨B, hB⟩ := hD
  exact hB.1.1

private theorem coupledWeakReference_inv_smooth (hD : IsAccumulatingProfile D) :
    ContDiffOn ℝ ∞ (fun r => (D.w r)⁻¹) (Ioo D.a D.b) :=
  (coupledWeakReference_smooth hD).contDiffOn.inv
    (fun r hr => (coupledWeakReference_positive hD r hr).ne')

private theorem coupledWeakReference_radius_inv_smooth (hD : IsAccumulatingProfile D) :
    ContDiffOn ℝ ∞ (fun r : ℝ => r⁻¹) (Ioo D.a D.b) :=
  contDiffOn_id.inv
    (fun r hr => ((coupledWeakReference_left_positive hD).trans hr.1).ne')

def coupledWeakReferenceWCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    CoupledWeakHeight S →L[ℝ] CoupledWeakHeight S :=
  SobolevModelData.radialMultiplierCLM (k := D.w) hT (hS.1 coupledWeakProfileWeight)
    ((coupledWeakReference_smooth hD).contDiffOn) (referenceProfile_material_subpower hD hT)

theorem decode_coupledWeakReferenceWCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : CoupledWeakHeight S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakReferenceWCLM hD hT hS u) p =
      (D.w) p.1 * (S.height coupledWeakProfileWeight).decode u p :=
  congrFun (SobolevModelData.decode_radialMultiplierCLM hT (hS.1 coupledWeakProfileWeight)
    ((coupledWeakReference_smooth hD).contDiffOn) (referenceProfile_material_subpower hD hT) u) p

theorem coupledWeakReferenceWCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (coupledWeakHeightGrading S) (coupledWeakHeightGrading S)
      (coupledWeakReferenceWCLM hD hT hS).toLinearMap 1 0 :=
  SobolevModelData.radialMultiplierCLM_isTame hT (hS.1 coupledWeakProfileWeight)
    ((coupledWeakReference_smooth hD).contDiffOn) (referenceProfile_material_subpower hD hT)

def coupledWeakReferenceInvWCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    CoupledWeakHeight S →L[ℝ] CoupledWeakHeight S :=
  SobolevModelData.radialMultiplierCLM (k := fun r => (D.w r)⁻¹) hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakReference_inv_smooth hD) (referenceInverse_material_subpower hD hT)

theorem decode_coupledWeakReferenceInvWCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : CoupledWeakHeight S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakReferenceInvWCLM hD hT hS u) p =
      (fun r => (D.w r)⁻¹) p.1 * (S.height coupledWeakProfileWeight).decode u p :=
  congrFun (SobolevModelData.decode_radialMultiplierCLM hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakReference_inv_smooth hD) (referenceInverse_material_subpower hD hT) u) p

theorem coupledWeakReferenceInvWCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (coupledWeakHeightGrading S) (coupledWeakHeightGrading S)
      (coupledWeakReferenceInvWCLM hD hT hS).toLinearMap 1 0 :=
  SobolevModelData.radialMultiplierCLM_isTame hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakReference_inv_smooth hD) (referenceInverse_material_subpower hD hT)

def coupledWeakReferenceInvRadiusCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    CoupledWeakHeight S →L[ℝ] CoupledWeakHeight S :=
  SobolevModelData.radialMultiplierCLM (k := fun r : ℝ => r⁻¹) hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakReference_radius_inv_smooth hD) (materialRadius_inv_subpower hD hT)

theorem decode_coupledWeakReferenceInvRadiusCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : CoupledWeakHeight S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakReferenceInvRadiusCLM hD hT hS u) p =
      (fun r : ℝ => r⁻¹) p.1 * (S.height coupledWeakProfileWeight).decode u p :=
  congrFun (SobolevModelData.decode_radialMultiplierCLM hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakReference_radius_inv_smooth hD) (materialRadius_inv_subpower hD hT) u) p

theorem coupledWeakReferenceInvRadiusCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (coupledWeakHeightGrading S) (coupledWeakHeightGrading S)
      (coupledWeakReferenceInvRadiusCLM hD hT hS).toLinearMap 1 0 :=
  SobolevModelData.radialMultiplierCLM_isTame hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakReference_radius_inv_smooth hD) (materialRadius_inv_subpower hD hT)


private theorem coupled_expPerturbation_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => Real.exp (a * t) - 1) :=
  (contDiff_const.mul contDiff_id).exp.sub contDiff_const

private theorem coupled_expPerturbation_zero (a : ℝ) :
    (fun t : ℝ => Real.exp (a * t) - 1) 0 = 0 := by simp

def coupledWeakHeightExp (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a : ℝ) (u : CoupledWeakHeight S) : CoupledWeakHeight S :=
  SobolevModelData.weightedCompositionMap hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakHeightInterpolation hS) coupledWeakProfileWeight_pos
    (coupled_expPerturbation_contDiff a) (coupled_expPerturbation_zero a) u

theorem decode_coupledWeakHeightExp (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (a : ℝ) (u : CoupledWeakHeight S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakHeightExp hT hS a u) p =
      Real.exp (a * (S.height coupledWeakProfileWeight).decode u p) - 1 :=
  congrFun (SobolevModelData.decode_weightedCompositionMap hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakHeightInterpolation hS) coupledWeakProfileWeight_pos
    (coupled_expPerturbation_contDiff a) (coupled_expPerturbation_zero a) u) p

def coupledWeakHeightInv (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : CoupledWeakHeight S) : CoupledWeakHeight S :=
  SobolevModelData.weightedCompositionMap hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakHeightInterpolation hS) coupledWeakProfileWeight_pos
    (scalarPowerPerturbation_contDiff (-1)) (scalarPowerPerturbation_zero (-1)) u

theorem decode_coupledWeakHeightInv (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (u : CoupledWeakHeight S) (p : PolarPoint)
    (hu : |(S.height coupledWeakProfileWeight).decode u p| ≤ 1 / 2) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakHeightInv hT hS u) p =
      (1 + (S.height coupledWeakProfileWeight).decode u p)⁻¹ - 1 :=
  (congrFun (SobolevModelData.decode_weightedCompositionMap hT (hS.1 coupledWeakProfileWeight)
    (coupledWeakHeightInterpolation hS) coupledWeakProfileWeight_pos
    (scalarPowerPerturbation_contDiff (-1)) (scalarPowerPerturbation_zero (-1)) u) p).trans
      (scalarPowerPerturbation_neg_one_eq hu)

section Germs

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X}
  {f g : X → CoupledWeakHeight S}

theorem UniformTameGerm.coupledWeakHeightMul
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f)
    (hg : UniformTameGerm p (coupledWeakHeightGrading S) x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakHeightMul hT hS (f x) (g x)) := by
  letI : ∀ n, CompleteSpace ((S.height coupledWeakProfileWeight).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 coupledWeakProfileWeight) n
  obtain ⟨base, loss, _, hB⟩ := SobolevModelData.decodedProductMap_twoFactor
    hT (hS.1 coupledWeakProfileWeight) (coupledWeakHeightInterpolation hS) coupledWeakProfileWeight_pos.le
  exact hf.bilinear hg
    (SobolevModelData.decodedProductMap hT (hS.1 coupledWeakProfileWeight)
      (coupledWeakHeightInterpolation hS) coupledWeakProfileWeight_pos.le 1)
    hB hp ht (coupledWeakHeightGrading_monotone S) (coupledWeakHeightGrading_withSeminorms S)

theorem UniformTameGerm.coupledWeakHeightUnitalMul
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f)
    (hg : UniformTameGerm p (coupledWeakHeightGrading S) x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakHeightUnitalMul hT hS (f x) (g x)) :=
  (hf.add hg hp ht).add (hf.coupledWeakHeightMul hg hT hS hp ht) hp ht

theorem UniformTameGerm.coupledWeakHeightUnitalAct
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f)
    (hg : UniformTameGerm p (coupledWeakHeightGrading S) x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakHeightUnitalAct hT hS (f x) (g x)) :=
  hg.add (hf.coupledWeakHeightMul hg hT hS hp ht) hp ht

theorem UniformTameGerm.coupledWeakHeightSMul {a : X → ℝ}
    (ha : UniformTameGerm p realGrading x0 a)
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f)
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0 (fun x => a x • f x) := by
  letI : ∀ n, CompleteSpace ((S.height coupledWeakProfileWeight).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 coupledWeakProfileWeight) n
  exact ha.smul hf hp ht (coupledWeakHeightGrading_monotone S)
    (coupledWeakHeightGrading_withSeminorms S)

theorem UniformTameGerm.coupledWeakReferenceW
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakReferenceWCLM hD hT hS (f x)) :=
  hf.postcompose hp ht (coupledWeakReferenceWCLM hD hT hS)
    (coupledWeakReferenceWCLM_isTame hD hT hS)

theorem UniformTameGerm.coupledWeakReferenceInvW
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakReferenceInvWCLM hD hT hS (f x)) :=
  hf.postcompose hp ht (coupledWeakReferenceInvWCLM hD hT hS)
    (coupledWeakReferenceInvWCLM_isTame hD hT hS)

theorem UniformTameGerm.coupledWeakReferenceInvRadius
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakReferenceInvRadiusCLM hD hT hS (f x)) :=
  hf.postcompose hp ht (coupledWeakReferenceInvRadiusCLM hD hT hS)
    (coupledWeakReferenceInvRadiusCLM_isTame hD hT hS)


theorem UniformTameGerm.coupledWeakHeightExp
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f) (hf0 : f x0 = 0)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (a : ℝ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakHeightExp hT hS a (f x)) :=
  hf.weightedComposition hf0 hT hS coupledWeakProfileWeight_pos
    (coupled_expPerturbation_contDiff a) (coupled_expPerturbation_zero a) hp ht

theorem UniformTameGerm.coupledWeakHeightInv
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f) (hf0 : f x0 = 0)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakHeightInv hT hS (f x)) :=
  hf.weightedComposition hf0 hT hS coupledWeakProfileWeight_pos
    (scalarPowerPerturbation_contDiff (-1)) (scalarPowerPerturbation_zero (-1)) hp ht

end Germs

end ContinuousFlexibility.Statements
