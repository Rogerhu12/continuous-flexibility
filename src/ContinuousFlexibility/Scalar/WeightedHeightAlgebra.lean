module

public import ContinuousFlexibility.Scalar.WeightedBinaryProduct
public import ContinuousFlexibility.Scalar.WeightedPhysicalMultiplier
public import ContinuousFlexibility.Scalar.WeightedReferenceMaterialJets
public import ContinuousFlexibility.Scalar.WeightedNeighborhood

/-!
# Concrete algebra on the scalar weighted heights

All operations below use the original Sobolev decoder. The reference
coefficients act as actual radial multipliers. Products with the constant
background one are expanded into sums and products of decaying heights.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarBeta_pos : 0 < scalarBeta := by norm_num [scalarBeta]

theorem scalarHeightInterpolation (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (scalarHeightGrading S) := (hS.2.2.2.1 scalarBeta).2.2

def scalarHeightMul (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) : ScalarHeightSpace S :=
  SobolevModelData.decodedProductMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos.le 1 ![u, v]

theorem decode_scalarHeightMul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarHeightMul hT hS u v) p =
      (S.height scalarBeta).decode u p * (S.height scalarBeta).decode v p :=
  congrFun (SobolevModelData.decode_decodedProductMap_two hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos.le ![u, v]) p

/-- The decaying part of the product of two fields with background one. -/
def scalarHeightUnitalMul (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) : ScalarHeightSpace S :=
  u + v + scalarHeightMul hT hS u v

/-- Multiplication of a decaying height by a field with background one. -/
def scalarHeightUnitalAct (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) : ScalarHeightSpace S :=
  v + scalarHeightMul hT hS u v

theorem decode_scalarHeightUnitalMul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarHeightUnitalMul hT hS u v) p =
      (1 + (S.height scalarBeta).decode u p) *
        (1 + (S.height scalarBeta).decode v p) - 1 := by
  simp only [scalarHeightUnitalMul, map_add, Pi.add_apply, decode_scalarHeightMul]
  ring

theorem decode_scalarHeightUnitalAct
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarHeightUnitalAct hT hS u v) p =
      (1 + (S.height scalarBeta).decode u p) * (S.height scalarBeta).decode v p := by
  simp only [scalarHeightUnitalAct, map_add, Pi.add_apply, decode_scalarHeightMul]
  ring

theorem scalarHeightMul_zero_left
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (u : ScalarHeightSpace S) :
    scalarHeightMul hT hS 0 u = 0 := by
  apply (hS.1 scalarBeta).2.2.2.2.2.1
  funext p
  simp only [decode_scalarHeightMul, map_zero, Pi.zero_apply, zero_mul]

theorem scalarHeightMul_zero_right
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (u : ScalarHeightSpace S) :
    scalarHeightMul hT hS u 0 = 0 := by
  apply (hS.1 scalarBeta).2.2.2.2.2.1
  funext p
  simp only [decode_scalarHeightMul, map_zero, Pi.zero_apply, mul_zero]

private theorem scalarReference_smooth (hD : IsAccumulatingProfile D) :
    ContDiff ℝ ∞ D.w := by
  obtain ⟨B, hB⟩ := hD
  exact hB.1.2.2.1.1

private theorem scalarReference_positive (hD : IsAccumulatingProfile D) :
    ∀ r ∈ Ioo D.a D.b, 0 < D.w r := by
  obtain ⟨B, hB⟩ := hD
  exact hB.1.2.2.2.2.1

private theorem scalarReference_left_positive (hD : IsAccumulatingProfile D) : 0 < D.a := by
  obtain ⟨B, hB⟩ := hD
  exact hB.1.1

private theorem scalarReference_inv_smooth (hD : IsAccumulatingProfile D) :
    ContDiffOn ℝ ∞ (fun r => (D.w r)⁻¹) (Ioo D.a D.b) :=
  (scalarReference_smooth hD).contDiffOn.inv
    (fun r hr => (scalarReference_positive hD r hr).ne')

private theorem scalarReference_radius_inv_smooth (hD : IsAccumulatingProfile D) :
    ContDiffOn ℝ ∞ (fun r : ℝ => r⁻¹) (Ioo D.a D.b) :=
  contDiffOn_id.inv
    (fun r hr => ((scalarReference_left_positive hD).trans hr.1).ne')

def scalarReferenceWCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarHeightSpace S →L[ℝ] ScalarHeightSpace S :=
  SobolevModelData.radialMultiplierCLM (k := D.w) hT (hS.1 scalarBeta)
    ((scalarReference_smooth hD).contDiffOn) (referenceProfile_material_subpower hD hT)

theorem decode_scalarReferenceWCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarReferenceWCLM hD hT hS u) p =
      (D.w) p.1 * (S.height scalarBeta).decode u p :=
  congrFun (SobolevModelData.decode_radialMultiplierCLM hT (hS.1 scalarBeta)
    ((scalarReference_smooth hD).contDiffOn) (referenceProfile_material_subpower hD hT) u) p

theorem scalarReferenceWCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarHeightGrading S) (scalarHeightGrading S)
      (scalarReferenceWCLM hD hT hS).toLinearMap 1 0 :=
  SobolevModelData.radialMultiplierCLM_isTame hT (hS.1 scalarBeta)
    ((scalarReference_smooth hD).contDiffOn) (referenceProfile_material_subpower hD hT)

def scalarReferenceWDerivCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarHeightSpace S →L[ℝ] ScalarHeightSpace S :=
  SobolevModelData.radialMultiplierCLM (k := deriv D.w) hT (hS.1 scalarBeta)
    (((contDiff_infty_iff_deriv.mp (scalarReference_smooth hD)).2).contDiffOn) (referenceProfile_deriv_material_subpower hD hT)

theorem decode_scalarReferenceWDerivCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarReferenceWDerivCLM hD hT hS u) p =
      (deriv D.w) p.1 * (S.height scalarBeta).decode u p :=
  congrFun (SobolevModelData.decode_radialMultiplierCLM hT (hS.1 scalarBeta)
    (((contDiff_infty_iff_deriv.mp (scalarReference_smooth hD)).2).contDiffOn) (referenceProfile_deriv_material_subpower hD hT) u) p

theorem scalarReferenceWDerivCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarHeightGrading S) (scalarHeightGrading S)
      (scalarReferenceWDerivCLM hD hT hS).toLinearMap 1 0 :=
  SobolevModelData.radialMultiplierCLM_isTame hT (hS.1 scalarBeta)
    (((contDiff_infty_iff_deriv.mp (scalarReference_smooth hD)).2).contDiffOn) (referenceProfile_deriv_material_subpower hD hT)

def scalarReferenceInvWCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarHeightSpace S →L[ℝ] ScalarHeightSpace S :=
  SobolevModelData.radialMultiplierCLM (k := fun r => (D.w r)⁻¹) hT (hS.1 scalarBeta)
    (scalarReference_inv_smooth hD) (referenceInverse_material_subpower hD hT)

theorem decode_scalarReferenceInvWCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarReferenceInvWCLM hD hT hS u) p =
      (fun r => (D.w r)⁻¹) p.1 * (S.height scalarBeta).decode u p :=
  congrFun (SobolevModelData.decode_radialMultiplierCLM hT (hS.1 scalarBeta)
    (scalarReference_inv_smooth hD) (referenceInverse_material_subpower hD hT) u) p

theorem scalarReferenceInvWCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarHeightGrading S) (scalarHeightGrading S)
      (scalarReferenceInvWCLM hD hT hS).toLinearMap 1 0 :=
  SobolevModelData.radialMultiplierCLM_isTame hT (hS.1 scalarBeta)
    (scalarReference_inv_smooth hD) (referenceInverse_material_subpower hD hT)

def scalarReferenceRadiusCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarHeightSpace S →L[ℝ] ScalarHeightSpace S :=
  SobolevModelData.radialMultiplierCLM (k := fun r : ℝ => r) hT (hS.1 scalarBeta)
    (contDiffOn_id) (materialRadius_subpower hT)

theorem decode_scalarReferenceRadiusCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarReferenceRadiusCLM hD hT hS u) p =
      (fun r : ℝ => r) p.1 * (S.height scalarBeta).decode u p :=
  congrFun (SobolevModelData.decode_radialMultiplierCLM hT (hS.1 scalarBeta)
    (contDiffOn_id) (materialRadius_subpower hT) u) p

theorem scalarReferenceRadiusCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarHeightGrading S) (scalarHeightGrading S)
      (scalarReferenceRadiusCLM hD hT hS).toLinearMap 1 0 :=
  SobolevModelData.radialMultiplierCLM_isTame hT (hS.1 scalarBeta)
    (contDiffOn_id) (materialRadius_subpower hT)

def scalarReferenceInvRadiusCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarHeightSpace S →L[ℝ] ScalarHeightSpace S :=
  SobolevModelData.radialMultiplierCLM (k := fun r : ℝ => r⁻¹) hT (hS.1 scalarBeta)
    (scalarReference_radius_inv_smooth hD) (materialRadius_inv_subpower hD hT)

theorem decode_scalarReferenceInvRadiusCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarReferenceInvRadiusCLM hD hT hS u) p =
      (fun r : ℝ => r⁻¹) p.1 * (S.height scalarBeta).decode u p :=
  congrFun (SobolevModelData.decode_radialMultiplierCLM hT (hS.1 scalarBeta)
    (scalarReference_radius_inv_smooth hD) (materialRadius_inv_subpower hD hT) u) p

theorem scalarReferenceInvRadiusCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarHeightGrading S) (scalarHeightGrading S)
      (scalarReferenceInvRadiusCLM hD hT hS).toLinearMap 1 0 :=
  SobolevModelData.radialMultiplierCLM_isTame hT (hS.1 scalarBeta)
    (scalarReference_radius_inv_smooth hD) (materialRadius_inv_subpower hD hT)

end ContinuousFlexibility.Statements
