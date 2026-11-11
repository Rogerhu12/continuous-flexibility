import ContinuousFlexibility.Radial.OuterTransferNorm

/-!
# The two outward state orientations

Reversing radial orientation changes the sign of the scaled flux.
That fixed reflection is an isometry for the actual product norm.
The outward left transfer is its conjugate of the inverse radial transfer,
so the sum of the two operator norms is unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

def outerFluxReflection : (ℝ × ℝ) ≃ₗᵢ[ℝ] (ℝ × ℝ) where
  toFun v := (v.1, -v.2)
  invFun v := (v.1, -v.2)
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by ext <;> simp [add_comm]
  map_smul' r v := by ext <;> simp
  norm_map' v := by
    change max |v.1| |-v.2| = max |v.1| |v.2|
    rw [abs_neg]

@[simp] theorem outerFluxReflection_apply (v : ℝ × ℝ) :
    outerFluxReflection v = (v.1, -v.2) := rfl

@[simp] theorem outerFluxReflection_twice (v : ℝ × ℝ) :
    outerFluxReflection (outerFluxReflection v) = v := by simp

def outerReflectedTransfer (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (outerFluxReflection.toContinuousLinearEquiv.trans A).trans
    outerFluxReflection.toContinuousLinearEquiv

@[simp] theorem outerReflectedTransfer_apply
    (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (v : ℝ × ℝ) :
    outerReflectedTransfer A v = outerFluxReflection (A (outerFluxReflection v)) := rfl

@[simp] theorem outerReflectedTransfer_symm
    (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    (outerReflectedTransfer A).symm = outerReflectedTransfer A.symm := by
  apply ContinuousLinearEquiv.ext
  funext v
  rfl

theorem outerReflectedTransfer_norm
    (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ‖(outerReflectedTransfer A).toContinuousLinearMap‖ = ‖A.toContinuousLinearMap‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    change ‖outerFluxReflection (A (outerFluxReflection v))‖ ≤
      ‖A.toContinuousLinearMap‖ * ‖v‖
    rw [outerFluxReflection.norm_map]
    exact (A.toContinuousLinearMap.le_opNorm _).trans_eq
      (congrArg (fun t => ‖A.toContinuousLinearMap‖ * t) (outerFluxReflection.norm_map v))
  · apply A.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _)
    intro v
    have h := (outerReflectedTransfer A).toContinuousLinearMap.le_opNorm (outerFluxReflection v)
    change ‖outerFluxReflection (A (outerFluxReflection (outerFluxReflection v)))‖ ≤
      ‖(outerReflectedTransfer A).toContinuousLinearMap‖ * ‖outerFluxReflection v‖ at h
    change ‖A v‖ ≤ ‖(outerReflectedTransfer A).toContinuousLinearMap‖ * ‖v‖
    simpa only [outerFluxReflection_twice, outerFluxReflection.norm_map] using h

/-- The true outward transfer, for either radial end. -/
def outerOutwardTransfer (right : Bool) (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  if right then A else outerReflectedTransfer A.symm

theorem outerOutwardTransfer_norm_sum (right : Bool)
    (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ‖(outerOutwardTransfer right A).toContinuousLinearMap‖ +
        ‖(outerOutwardTransfer right A).symm.toContinuousLinearMap‖ =
      ‖A.toContinuousLinearMap‖ + ‖A.symm.toContinuousLinearMap‖ := by
  cases right
  · change ‖(outerReflectedTransfer A.symm).toContinuousLinearMap‖ +
        ‖(outerReflectedTransfer A.symm).symm.toContinuousLinearMap‖ = _
    rw [outerReflectedTransfer_symm, ContinuousLinearEquiv.symm_symm,
      outerReflectedTransfer_norm, outerReflectedTransfer_norm]
    exact add_comm _ _
  · rfl

/-- The outward operator is exactly the endpoint map for the reflected
left value/flux state, including when either value is zero. -/
theorem outerOutwardTransfer_actual (right : Bool)
    (A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) {l r : ℝ × ℝ} (h : A l = r) :
    outerOutwardTransfer right A
        (if right then l else outerFluxReflection r) =
      if right then r else outerFluxReflection l := by
  cases right
  · change outerFluxReflection (A.symm (outerFluxReflection (outerFluxReflection r))) =
      outerFluxReflection l
    rw [outerFluxReflection_twice, ← h, A.symm_apply_apply]
  · exact h

end ContinuousFlexibility.Radial
