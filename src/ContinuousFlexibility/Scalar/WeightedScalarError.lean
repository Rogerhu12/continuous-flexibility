import ContinuousFlexibility.Scalar.WeightedScalarOperator

/-!
# The actual correction error from its normalized type coefficient

Only the product of the singular type coefficient with a weighted height is
extended. A decaying perturbation of w times that coefficient determines this
product through the actual reciprocal-reference multiplier. Angular integration
and two actual angular derivatives then construct the bilinear correction error.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- Multiplication by the fixed radial background (1 + w²)/r. -/
def scalarReferenceTypeCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ScalarHeightSpace S →L[ℝ] ScalarHeightSpace S :=
  (scalarReferenceInvRadiusCLM hD hT hS).comp
    (ContinuousLinearMap.id ℝ _ +
      (scalarReferenceWCLM hD hT hS).comp (scalarReferenceWCLM hD hT hS))

private theorem scalarReferenceTypeCLM_isTame_aux
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] {p : ℕ → Seminorm ℝ E}
    (L W : E →L[ℝ] E) (hp : Monotone p)
    (hL : IsTameLinear p p L.toLinearMap 1 0)
    (hW : IsTameLinear p p W.toLinearMap 1 0) :
    IsTameLinear p p
      (L.comp (ContinuousLinearMap.id ℝ E + W.comp W)).toLinearMap 3 0 := by
  have hmap : (L.comp (ContinuousLinearMap.id ℝ E + W.comp W)).toLinearMap =
      L.toLinearMap.comp ((LinearMap.id : E →ₗ[ℝ] E) +
        W.toLinearMap.comp W.toLinearMap) := by
    ext u
    rfl
  rw [hmap]
  exact hL.comp ((IsTameLinear.id p).add hp (hW.comp hW))

theorem scalarReferenceTypeCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarHeightGrading S) (scalarHeightGrading S)
      (scalarReferenceTypeCLM hD hT hS).toLinearMap 3 0 :=
  scalarReferenceTypeCLM_isTame_aux (scalarReferenceInvRadiusCLM hD hT hS)
    (scalarReferenceWCLM hD hT hS) (scalarHeightGrading_monotone S)
    (scalarReferenceInvRadiusCLM_isTame hD hT hS) (scalarReferenceWCLM_isTame hD hT hS)

theorem decode_scalarReferenceTypeCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (R : ScalarHeightSpace S) :
    (S.height scalarBeta).decode (scalarReferenceTypeCLM hD hT hS R) =
      fun p => ((1 + D.w p.1 ^ 2) / p.1) * (S.height scalarBeta).decode R p := by
  funext p
  change (S.height scalarBeta).decode
    (scalarReferenceInvRadiusCLM hD hT hS
      (R + scalarReferenceWCLM hD hT hS (scalarReferenceWCLM hD hT hS R))) p = _
  rw [decode_scalarReferenceInvRadiusCLM, map_add]
  simp only [Pi.add_apply, decode_scalarReferenceWCLM, div_eq_mul_inv]
  ring

def scalarTypeMultiplierCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : ScalarHeightSpace S) : ScalarHeightSpace S →L[ℝ] ScalarHeightSpace S :=
  let M := SobolevModelData.decodedProductMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos.le 1
  (scalarReferenceInvWCLM hD hT hS).comp
    (scalarReferenceTypeCLM hD hT hS + scalarBilinearFixLeft M t)

theorem scalarTypeMultiplierCLM_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t R : ScalarHeightSpace S) :
    scalarTypeMultiplierCLM hD hT hS t R =
      scalarReferenceInvWCLM hD hT hS
        (scalarReferenceTypeCLM hD hT hS R + scalarHeightMul hT hS t R) := by
  simp only [scalarTypeMultiplierCLM, ContinuousLinearMap.comp_apply, add_apply,
    scalarBilinearFixLeft_apply] <;> rfl

theorem decode_scalarTypeMultiplierCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t R : ScalarHeightSpace S) :
    (S.height scalarBeta).decode (scalarTypeMultiplierCLM hD hT hS t R) =
      fun p => (D.w p.1)⁻¹ *
        (((1 + D.w p.1 ^ 2) / p.1 + (S.height scalarBeta).decode t p) *
          (S.height scalarBeta).decode R p) := by
  rw [scalarTypeMultiplierCLM_apply]
  funext p
  rw [decode_scalarReferenceInvWCLM, map_add]
  simp only [Pi.add_apply, decode_scalarReferenceTypeCLM, decode_scalarHeightMul]
  ring

/-- An interior normalized coefficient identity is enough: outside the
annulus both products vanish by the actual height support. -/
theorem decode_scalarTypeMultiplierCLM_of_actual
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : ScalarHeightSpace S) (F : PolarPoint → ℝ)
    (ht : ∀ p ∈ annularOpen D, (S.height scalarBeta).decode t p =
      D.w p.1 * F p - (1 + D.w p.1 ^ 2) / p.1)
    (R : ScalarHeightSpace S) :
    (S.height scalarBeta).decode (scalarTypeMultiplierCLM hD hT hS t R) =
      fun p => F p * (S.height scalarBeta).decode R p := by
  rw [decode_scalarTypeMultiplierCLM]
  funext p
  by_cases hp : p ∈ annularOpen D
  · have hw : D.w p.1 ≠ 0 := (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1).ne'
    rw [ht p hp]
    have he : (1 + D.w p.1 ^ 2) / p.1 +
        (D.w p.1 * F p - (1 + D.w p.1 ^ 2) / p.1) = D.w p.1 * F p := by ring
    rw [he]
    field_simp [hw] <;> ring
  · rw [((hS.1 scalarBeta).2.2.2.1 R).2.2.2.1 p hp]
    simp only [mul_zero]

def scalarTypeErrorCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t R : ScalarHeightSpace S) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  let P := SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos
  (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)).comp
    ((scalarBilinearFixLeft P (scalarTypeMultiplierCLM hD hT hS t R)).comp
      (scalarCommonProjectionCLM S))

theorem scalarTypeErrorCLM_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t R : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    scalarTypeErrorCLM hD hT hS t R u =
      SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)
        (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
          (scalarHeightInterpolation hS) scalarBeta_pos
          ![scalarTypeMultiplierCLM hD hT hS t R, u.1]) := by
  simp only [scalarTypeErrorCLM, ContinuousLinearMap.comp_apply,
    scalarBilinearFixLeft_apply] <;> rfl

/-- The correction error is genuinely linear in each independent height
argument, with no topology imposed on the space of curried operators. -/
def scalarTypeErrorLinear
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : ScalarHeightSpace S) :
    ScalarHeightSpace S →ₗ[ℝ] ScalarCommonHeight S →ₗ[ℝ] ScalarHeightSpace S where
  toFun R := (scalarTypeErrorCLM hD hT hS t R).toLinearMap
  map_add' := by
    intro R₁ R₂
    ext u
    change scalarTypeErrorCLM hD hT hS t (R₁ + R₂) u =
      scalarTypeErrorCLM hD hT hS t R₁ u + scalarTypeErrorCLM hD hT hS t R₂ u
    simp only [scalarTypeErrorCLM_apply, map_add]
    have he := (scalarBilinearFixRight
      (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
        (scalarHeightInterpolation hS) scalarBeta_pos) u.1).map_add
          (scalarTypeMultiplierCLM hD hT hS t R₁) (scalarTypeMultiplierCLM hD hT hS t R₂)
    simp only [scalarBilinearFixRight_apply] at he
    rw [he, map_add]
  map_smul' := by
    intro c R
    ext u
    change scalarTypeErrorCLM hD hT hS t (c • R) u =
      c • scalarTypeErrorCLM hD hT hS t R u
    simp only [scalarTypeErrorCLM_apply, map_smul]
    have he := (scalarBilinearFixRight
      (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
        (scalarHeightInterpolation hS) scalarBeta_pos) u.1).map_smul c
          (scalarTypeMultiplierCLM hD hT hS t R)
    simp only [scalarBilinearFixRight_apply] at he
    rw [he, map_smul]

theorem scalarTypeErrorLinear_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t R : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    scalarTypeErrorLinear hD hT hS t R u = scalarTypeErrorCLM hD hT hS t R u := rfl

theorem decode_scalarTypeErrorLinear_of_actual
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : ScalarHeightSpace S) (F : PolarPoint → ℝ)
    (ht : ∀ p ∈ annularOpen D, (S.height scalarBeta).decode t p =
      D.w p.1 * F p - (1 + D.w p.1 ^ 2) / p.1)
    (R : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode (scalarTypeErrorLinear hD hT hS t R u) =
      scalarCorrectionError F ((S.height scalarBeta).decode R) (scalarCommonHeightDecode S u) := by
  rw [scalarTypeErrorLinear_apply, scalarTypeErrorCLM_apply,
    SobolevModelData.decode_angularSecondCLM,
    SobolevModelData.angularPartial_decode_oddProductPrimitiveMap]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    decode_scalarTypeMultiplierCLM_of_actual hD hT hS t F ht R]
  rw [← scalarCommonHeightDecode_angularPartial hT hS u] <;> rfl

end ContinuousFlexibility.Statements
