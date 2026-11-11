import ContinuousFlexibility.Analysis.CoupledMixedWeightAction
import ContinuousFlexibility.Analysis.CoupledWeakHeightCalculus
import ContinuousFlexibility.Scalar.WeightedScalarError
import ContinuousFlexibility.Scalar.WeightedErrorConservation

/-!
# The actual scalar correction error with a weak normalized coefficient

The normalized type perturbation only has the positive profile weight.
Its product with the independent source retains the original strong weight.
The angular primitive and its second derivative then give an actual Source,
linear in both independent arguments, for every weak coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def coupledWeakTypeMultiplierCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) : ScalarHeightSpace S →L[ℝ] ScalarHeightSpace S :=
  (scalarReferenceInvWCLM hD hT hS).comp
    (scalarReferenceTypeCLM hD hT hS +
      coupledMixedWeightActionCLM hT hS coupledWeakProfileWeight_pos.le scalarBeta t)

theorem coupledWeakTypeMultiplierCLM_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (R : ScalarHeightSpace S) :
    coupledWeakTypeMultiplierCLM hD hT hS t R =
      scalarReferenceInvWCLM hD hT hS
        (scalarReferenceTypeCLM hD hT hS R +
          coupledMixedWeightAction hT hS coupledWeakProfileWeight_pos.le scalarBeta t R) := by
  simp only [coupledWeakTypeMultiplierCLM, ContinuousLinearMap.comp_apply, add_apply,
    coupledMixedWeightActionCLM_apply]

theorem coupledWeakTypeMultiplierCLM_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (R : ScalarHeightSpace S) :
    (S.height scalarBeta).decode (coupledWeakTypeMultiplierCLM hD hT hS t R) =
      fun p => (D.w p.1)⁻¹ *
        (((1 + D.w p.1 ^ 2) / p.1 + (S.height coupledWeakProfileWeight).decode t p) *
          (S.height scalarBeta).decode R p) := by
  have hsum := scalarHeightDecode_add S (scalarReferenceTypeCLM hD hT hS R)
    (coupledMixedWeightAction hT hS coupledWeakProfileWeight_pos.le scalarBeta t R)
  have htype := decode_scalarReferenceTypeCLM hD hT hS R
  funext p
  apply (congrArg (fun v : ScalarHeightSpace S => (S.height scalarBeta).decode v p)
    (coupledWeakTypeMultiplierCLM_apply hD hT hS t R)).trans
  apply (decode_scalarReferenceInvWCLM hD hT hS
    (scalarReferenceTypeCLM hD hT hS R +
      coupledMixedWeightAction hT hS coupledWeakProfileWeight_pos.le scalarBeta t R) p).trans
  calc
    _ = (D.w p.1)⁻¹ *
        (((1 + D.w p.1 ^ 2) / p.1) * (S.height scalarBeta).decode R p +
          (S.height coupledWeakProfileWeight).decode t p * (S.height scalarBeta).decode R p) :=
      congrArg (fun z : ℝ => (D.w p.1)⁻¹ * z)
        ((congrFun hsum p).trans
          (congrArg₂ (fun x y : ℝ => x + y) (congrFun htype p)
            (coupledMixedWeightAction_decode hT hS coupledWeakProfileWeight_pos.le
              scalarBeta t R p)))
    _ = _ := by ring

/-- Only the interior coefficient identity is needed, because the strong
source has its prescribed zero extension outside the annulus. -/
theorem coupledWeakTypeMultiplierCLM_decode_of_actual
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (F : PolarPoint → ℝ)
    (ht : ∀ p ∈ annularOpen D, (S.height coupledWeakProfileWeight).decode t p =
      D.w p.1 * F p - (1 + D.w p.1 ^ 2) / p.1)
    (R : ScalarHeightSpace S) :
    (S.height scalarBeta).decode (coupledWeakTypeMultiplierCLM hD hT hS t R) =
      fun p => F p * (S.height scalarBeta).decode R p := by
  rw [coupledWeakTypeMultiplierCLM_decode hD hT hS t R]
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

def coupledWeakTypeErrorCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (R : ScalarHeightSpace S) :
    HeightPair S →L[ℝ] ScalarHeightSpace S :=
  let P := SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos
  (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)).comp
    ((scalarBilinearFixLeft P (coupledWeakTypeMultiplierCLM hD hT hS t R)).comp
      (scalarCommonProjectionCLM S))

theorem coupledWeakTypeErrorCLM_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (R : ScalarHeightSpace S) (u : HeightPair S) :
    coupledWeakTypeErrorCLM hD hT hS t R u =
      SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)
        (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
          (scalarHeightInterpolation hS) scalarBeta_pos
          ![coupledWeakTypeMultiplierCLM hD hT hS t R, u.1]) := by
  simp only [coupledWeakTypeErrorCLM, ContinuousLinearMap.comp_apply,
    scalarBilinearFixLeft_apply] <;> rfl

private theorem coupled_weak_error_bilinear_add
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (A L : E →L[ℝ] E) (P : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)
    (x y v : E) :
    A (P ![L (x + y), v]) = A (P ![L x, v]) + A (P ![L y, v]) := by
  have he := (A.comp ((scalarBilinearFixRight P v).comp L)).map_add x y
  simpa only [ContinuousLinearMap.comp_apply, scalarBilinearFixRight_apply] using he

private theorem coupled_weak_error_bilinear_smul
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (A L : E →L[ℝ] E) (P : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)
    (c : ℝ) (x v : E) :
    A (P ![L (c • x), v]) = c • A (P ![L x, v]) := by
  have he := (A.comp ((scalarBilinearFixRight P v).comp L)).map_smul c x
  simpa only [ContinuousLinearMap.comp_apply, scalarBilinearFixRight_apply] using he

def coupledWeakTypeErrorLinear
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) :
    ScalarHeightSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] ScalarHeightSpace S where
  toFun R := (coupledWeakTypeErrorCLM hD hT hS t R).toLinearMap
  map_add' := by
    intro R₁ R₂
    apply LinearMap.ext
    intro u
    change coupledWeakTypeErrorCLM hD hT hS t (R₁ + R₂) u =
      coupledWeakTypeErrorCLM hD hT hS t R₁ u + coupledWeakTypeErrorCLM hD hT hS t R₂ u
    exact (coupledWeakTypeErrorCLM_apply hD hT hS t (R₁ + R₂) u).trans
      ((coupled_weak_error_bilinear_add
        (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta))
        (coupledWeakTypeMultiplierCLM hD hT hS t)
        (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
          (scalarHeightInterpolation hS) scalarBeta_pos) R₁ R₂ u.1).trans
        (congrArg₂ (fun x y : ScalarHeightSpace S => x + y)
          (coupledWeakTypeErrorCLM_apply hD hT hS t R₁ u).symm
          (coupledWeakTypeErrorCLM_apply hD hT hS t R₂ u).symm))
  map_smul' := by
    intro c R
    apply LinearMap.ext
    intro u
    change coupledWeakTypeErrorCLM hD hT hS t (c • R) u =
      c • coupledWeakTypeErrorCLM hD hT hS t R u
    exact (coupledWeakTypeErrorCLM_apply hD hT hS t (c • R) u).trans
      ((coupled_weak_error_bilinear_smul
        (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta))
        (coupledWeakTypeMultiplierCLM hD hT hS t)
        (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
          (scalarHeightInterpolation hS) scalarBeta_pos) c R u.1).trans
        (congrArg (fun v : ScalarHeightSpace S => c • v)
          (coupledWeakTypeErrorCLM_apply hD hT hS t R u).symm))

theorem coupledWeakTypeErrorLinear_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (R : ScalarHeightSpace S) (u : HeightPair S) :
    coupledWeakTypeErrorLinear hD hT hS t R u = coupledWeakTypeErrorCLM hD hT hS t R u := rfl

theorem coupledWeakTypeErrorLinear_decode_of_actual
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (F : PolarPoint → ℝ)
    (ht : ∀ p ∈ annularOpen D, (S.height coupledWeakProfileWeight).decode t p =
      D.w p.1 * F p - (1 + D.w p.1 ^ 2) / p.1)
    (R : ScalarHeightSpace S) (u : HeightPair S) :
    (S.height scalarBeta).decode (coupledWeakTypeErrorLinear hD hT hS t R u) =
      scalarCorrectionError F ((S.height scalarBeta).decode R) (heightPairField S u) := by
  have he := (coupledWeakTypeErrorLinear_apply hD hT hS t R u).trans
    (coupledWeakTypeErrorCLM_apply hD hT hS t R u)
  have hθ := SobolevModelData.decode_angularSecondCLM hT (hS.1 scalarBeta)
    (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
      (scalarHeightInterpolation hS) scalarBeta_pos
      ![coupledWeakTypeMultiplierCLM hD hT hS t R, u.1])
  have hP := SobolevModelData.angularPartial_decode_oddProductPrimitiveMap hT
    (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos
    ![coupledWeakTypeMultiplierCLM hD hT hS t R, u.1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hP
  have htype := coupledWeakTypeMultiplierCLM_decode_of_actual hD hT hS t F ht R
  have hu := scalarCommonHeightDecode_angularPartial hT hS u
  have hflux : angularPartial ((S.height scalarBeta).decode
      (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
        (scalarHeightInterpolation hS) scalarBeta_pos
        ![coupledWeakTypeMultiplierCLM hD hT hS t R, u.1])) =
      fun p => F p * (S.height scalarBeta).decode R p * angularPartial (heightPairField S u) p := by
    apply hP.trans
    funext p
    exact congrArg₂ (fun x y : ℝ => x * y) (congrFun htype p) (congrFun hu.symm p)
  exact (congrArg (S.height scalarBeta).decode he).trans
    (hθ.trans (congrArg angularPartial hflux))

theorem coupledWeakTypeErrorLinear_compatible
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (R : ScalarHeightSpace S) (u : HeightPair S) :
    S.Q (coupledWeakTypeErrorLinear hD hT hS t R u) = 0 := by
  have hQ : ∀ f : ScalarHeightSpace S,
      S.Q f = physicalSourceIntegral D ((S.height scalarBeta).decode f) :=
    hS.2.2.2.2.2.2.2.1
  rw [coupledWeakTypeErrorLinear_apply, coupledWeakTypeErrorCLM_apply,
    hQ, SobolevModelData.decode_angularSecondCLM]
  have hu := (hS.1 scalarBeta).2.2.2.1
    (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
      (scalarHeightInterpolation hS) scalarBeta_pos
      ![coupledWeakTypeMultiplierCLM hD hT hS t R, u.1])
  exact physicalSourceIntegral_angularPartial_eq_zero hD.choose_spec.1.2.1.le
    (scalar_contDiffOn_angularPartial (isOpen_Ioo.prod isOpen_univ) hu.1)
    (periodic_angularPartial hu.2.2.1)

/-- The weak coefficient yields an actual Source-valued bilinear error. -/
def coupledWeakTypeErrorSourceLinear
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) :
    ScalarHeightSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source where
  toFun R := (coupledWeakTypeErrorLinear hD hT hS t R).codRestrict S.Q.toLinearMap.ker
    (fun u => coupledWeakTypeErrorLinear_compatible hD hT hS t R u)
  map_add' := by
    intro R₁ R₂
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, map_add, LinearMap.add_apply, Submodule.coe_add] <;> rfl
  map_smul' := by
    intro c R
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, map_smul, LinearMap.smul_apply,
      Submodule.coe_smul, RingHom.id_apply] <;> rfl

theorem coupledWeakTypeErrorSourceLinear_val
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (R : ScalarHeightSpace S) (u : HeightPair S) :
    (coupledWeakTypeErrorSourceLinear hD hT hS t R u).val =
      coupledWeakTypeErrorLinear hD hT hS t R u :=
  LinearMap.codRestrict_apply _ _ _

theorem coupledWeakTypeErrorSourceLinear_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (t : CoupledWeakHeight S) (F : PolarPoint → ℝ)
    (ht : ∀ p ∈ annularOpen D, (S.height coupledWeakProfileWeight).decode t p =
      D.w p.1 * F p - (1 + D.w p.1 ^ 2) / p.1)
    (R : ScalarHeightSpace S) (u : HeightPair S) :
    (S.height scalarBeta).decode (coupledWeakTypeErrorSourceLinear hD hT hS t R u).val =
      scalarCorrectionError F ((S.height scalarBeta).decode R) (heightPairField S u) :=
  (congrArg (S.height scalarBeta).decode
    (coupledWeakTypeErrorSourceLinear_val hD hT hS t R u)).trans
      (coupledWeakTypeErrorLinear_decode_of_actual hD hT hS t F ht R u)

end ContinuousFlexibility.Statements
