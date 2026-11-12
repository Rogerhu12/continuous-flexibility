import ContinuousFlexibility.Analysis.CoupledControlCircleInverse
import ContinuousFlexibility.Analysis.CoupledControlNorms

/-!
# The feedback inverse on the original constant-circle space

The Banach Neumann solution is used only for its weighted mean. The full
constant control is recovered by the reciprocal diagonal from a smooth
circle-valued response. Both inverse identities hold on the original
constant-circle space, without a lift of arbitrary Banach controls.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section FeedbackAlgebra

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

private theorem coupled_feedback_preconditioned_sub
    (ρ : E →ₗ[ℝ] F) (j : F →ₗ[ℝ] F) (a : E → E) (h : F → E)
    (k : F → F) (q : ℝ)
    (ha : ∀ u, j (ρ (a u)) = ρ u) (hh : ∀ v, j (ρ (h v)) = q • k v) (u : E) :
    j (ρ (a u - h (ρ u))) = ρ u - q • k (ρ u) := by
  rw [map_sub, map_sub, ha, hh]

private theorem coupled_feedback_restriction_of_equation
    (ρ : E →ₗ[ℝ] F) (j : F →ₗ[ℝ] F) (i : E → E) (h : F → E)
    (k : F → F) (q : ℝ)
    (hi : ∀ v, ρ (i v) = j (ρ v)) (hh : ∀ v, j (ρ (h v)) = q • k v)
    (u : E) (ξ : F) (hξ : ξ - q • k ξ = j (ρ u)) :
    ρ (i (u + h ξ)) = ξ := by
  rw [hi, map_add, map_add, hh]
  exact (sub_eq_iff_eq_add.mp hξ).symm

private theorem coupled_feedback_left_of_formulas
    (a i op inv : E → E) (h : F → E) (ρ ξ : E → F)
    (hop : ∀ u, op u = a u - h (ρ u))
    (hinv : ∀ u, inv u = i (u + h (ξ u)))
    (hξ : ∀ u, ξ (op u) = ρ u) (hi : ∀ u, i (a u) = u) (u : E) :
    inv (op u) = u := by
  rw [hinv, hξ, hop, sub_add_cancel, hi]

private theorem coupled_feedback_right_of_formulas
    (a i op inv : E → E) (h : F → E) (ρ ξ : E → F)
    (hop : ∀ u, op u = a u - h (ρ u))
    (hinv : ∀ u, inv u = i (u + h (ξ u)))
    (hρ : ∀ u, ρ (inv u) = ξ u) (hi : ∀ u, a (i u) = u) (u : E) :
    op (inv u) = u := by
  rw [hop, hρ, hinv, hi, add_sub_cancel_right]

private theorem coupled_feedback_grading_add_bound
    (p : Seminorm ℝ E) (i : E → E) (hi : ∀ u, p (i u) ≤ 2 * p u) (u v : E) :
    p (i (u + v)) ≤ 2 * p u + 2 * p v :=
  (hi (u + v)).trans ((mul_le_mul_of_nonneg_left
    (map_add_le_add p u v) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

end FeedbackAlgebra

private theorem coupled_feedback_two_operator_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n j : F →L[ℝ] F) (hn : ‖n‖ ≤ 2) (hj : ‖j‖ ≤ 2) (u : F) :
    ‖n (j u)‖ ≤ 4 * ‖u‖ := by
  have hn' : ‖n (j u)‖ ≤ 2 * ‖j u‖ :=
    (n.le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hj' : ‖j u‖ ≤ 2 * ‖u‖ :=
    (j.le_opNorm _).trans (mul_le_mul_of_nonneg_right hj (norm_nonneg _))
  exact hn'.trans ((mul_le_mul_of_nonneg_left hj'
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

variable {T : MaterialData} {S : PhysicalSpacesData}
variable (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
  (B : ControlColumnData S) (G : ScalarInverseData S) (z : AnnularState S × ℝ)

def coupledConstantControlRestriction :
    CoupledConstantCircle hS →L[ℝ] ControlBanach :=
  B.restriction.comp (coupledConstantCircleSubmodule hS).subtypeL

theorem coupledConstantControlRestriction_apply (u : CoupledConstantCircle hS) :
    coupledConstantControlRestriction hS B u = B.restriction u.val := rfl

/-- The mean of the actual scaled height response, with its smooth
constant-circle codomain. -/
def coupledConstantHeightResponse : ControlBanach →L[ℝ] CoupledConstantCircle hS :=
  (coupledConstantCircleProjection hS).comp
    ((z.2 • B.heightRow z).comp (controlHeightResponse S B G z))

theorem coupledConstantHeightResponse_apply (u : ControlBanach) :
    coupledConstantHeightResponse hS B G z u =
      coupledConstantCircleProjection hS
        (z.2 • B.heightRow z (controlHeightResponse S B G z u)) := rfl

def coupledConstantFeedbackOperator :
    CoupledConstantCircle hS →L[ℝ] CoupledConstantCircle hS :=
  coupledControlCircleOperator hS B z -
    (coupledConstantHeightResponse hS B G z).comp (coupledConstantControlRestriction hS B)

theorem coupledConstantFeedbackOperator_apply (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackOperator hS B G z u = coupledControlCircleOperator hS B z u -
      coupledConstantHeightResponse hS B G z (coupledConstantControlRestriction hS B u) := rfl

/-- The Banach mean of the recovered inverse. -/
def coupledConstantFeedbackControl : CoupledConstantCircle hS →L[ℝ] ControlBanach :=
  ((coupledControlInverse S B G).inverse z).comp
    ((B.JInverse z).comp (coupledConstantControlRestriction hS B))

theorem coupledConstantFeedbackControl_apply (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackControl hS B G z u = (coupledControlInverse S B G).inverse z
      (B.JInverse z (coupledConstantControlRestriction hS B u)) := rfl

/-- Recovery in the actual constant-circle space after the base-space
Neumann solve. All maps are total; the identities below specify the domain. -/
def coupledConstantFeedbackInverse :
    CoupledConstantCircle hS →L[ℝ] CoupledConstantCircle hS :=
  (coupledControlCircleInverse hS B z).comp
    (ContinuousLinearMap.id ℝ (CoupledConstantCircle hS) +
      (coupledConstantHeightResponse hS B G z).comp (coupledConstantFeedbackControl hS B G z))

theorem coupledConstantFeedbackInverse_apply (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackInverse hS B G z u = coupledControlCircleInverse hS B z
      (u + coupledConstantHeightResponse hS B G z (coupledConstantFeedbackControl hS B G z u)) := rfl

variable
  (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
    angularMean ((S.circle (3 / 4 : ℝ)).decode u m))

include hrestriction in
theorem coupledConstantControlRestriction_projection (u : CircleSpace S) :
    coupledConstantControlRestriction hS B (coupledConstantCircleProjection hS u) =
      B.restriction u := by
  exact (coupledConstantControlRestriction_apply hS B
    (coupledConstantCircleProjection hS u)).trans
      ((congrArg (fun v : CircleSpace S => B.restriction v)
        (coupledConstantCircleProjection_val hS u)).trans
          (controlRestriction_angularMeanProjection hS B hrestriction u))

include hrestriction in
theorem coupledConstantHeightResponse_restriction (u : ControlBanach) :
    coupledConstantControlRestriction hS B (coupledConstantHeightResponse hS B G z u) =
      z.2 • controlMeanRow S B z (controlHeightResponse S B G z u) := by
  exact (congrArg (fun v : CoupledConstantCircle hS => coupledConstantControlRestriction hS B v)
    (coupledConstantHeightResponse_apply hS B G z u)).trans
      ((coupledConstantControlRestriction_projection hS B hrestriction
        (z.2 • B.heightRow z (controlHeightResponse S B G z u))).trans
          (((B.restriction).map_smul z.2 _).trans
            (congrArg (fun v : ControlBanach => z.2 • v)
              (controlMeanRow_apply B z (controlHeightResponse S B G z u)).symm)))

include hrestriction in
private theorem coupledConstantHeightResponse_preconditioned (u : ControlBanach) :
    B.JInverse z (coupledConstantControlRestriction hS B
      (coupledConstantHeightResponse hS B G z u)) = z.2 • controlFeedback S B G z u :=
  (congrArg (fun v : ControlBanach => B.JInverse z v)
    (coupledConstantHeightResponse_restriction hS B G z hrestriction u)).trans
      (((B.JInverse z).map_smul z.2 _).trans
        (congrArg (fun v : ControlBanach => z.2 • v) (controlFeedback_apply B G z u).symm))

variable
  (hcolumn : ∀ u, B.restriction (B.circleColumn z u) = B.J z (B.restriction u))
  (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
  (hJ : ∀ u, B.JInverse z (B.J z u) = u ∧ B.J z (B.JInverse z u) = u)
  (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|)
  (hsmall : ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ))

include hrestriction hcolumn hJ in
theorem coupledConstantFeedbackOperator_preconditioned_restriction
    (u : CoupledConstantCircle hS) :
    B.JInverse z (coupledConstantControlRestriction hS B
      (coupledConstantFeedbackOperator hS B G z u)) =
      coupledConstantControlRestriction hS B u - z.2 • controlFeedback S B G z
        (coupledConstantControlRestriction hS B u) := by
  have ha (v : CoupledConstantCircle hS) :
      B.JInverse z (coupledConstantControlRestriction hS B (coupledControlCircleOperator hS B z v)) =
        coupledConstantControlRestriction hS B v :=
    (congrArg (fun w : ControlBanach => B.JInverse z w)
      (coupledControlCircleOperator_restriction hS B z hrestriction hcolumn v)).trans
        (hJ (B.restriction v.val)).1
  exact (congrArg (fun v : CoupledConstantCircle hS =>
    B.JInverse z (coupledConstantControlRestriction hS B v))
      (coupledConstantFeedbackOperator_apply hS B G z u)).trans
        (coupled_feedback_preconditioned_sub (coupledConstantControlRestriction hS B).toLinearMap
          (B.JInverse z).toLinearMap (coupledControlCircleOperator hS B z)
          (coupledConstantHeightResponse hS B G z) (controlFeedback S B G z) z.2 ha
          (coupledConstantHeightResponse_preconditioned hS B G z hrestriction) u)

include hrestriction hcolumn hJ hsmall in
theorem coupledConstantFeedbackControl_operator (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackControl hS B G z (coupledConstantFeedbackOperator hS B G z u) =
      coupledConstantControlRestriction hS B u := by
  exact (coupledConstantFeedbackControl_apply hS B G z
    (coupledConstantFeedbackOperator hS B G z u)).trans
      ((congrArg (fun v : ControlBanach => (coupledControlInverse S B G).inverse z v)
        (coupledConstantFeedbackOperator_preconditioned_restriction hS B G z
          hrestriction hcolumn hJ u)).trans
            (coupledControlInverse_left B G z hsmall (coupledConstantControlRestriction hS B u)))

include hrestriction hdiag hJ hlo hsmall in
/-- The circle recovery has exactly the same mean as the Banach solution. -/
theorem coupledConstantFeedbackInverse_restriction (u : CoupledConstantCircle hS) :
    coupledConstantControlRestriction hS B (coupledConstantFeedbackInverse hS B G z u) =
      coupledConstantFeedbackControl hS B G z u := by
  have hinv (v : CoupledConstantCircle hS) :
      coupledConstantControlRestriction hS B (coupledControlCircleInverse hS B z v) =
        B.JInverse z (coupledConstantControlRestriction hS B v) :=
    coupledControlCircleInverse_restriction hS B z hrestriction hdiag (fun v => (hJ v).2) hlo v
  have hN : coupledConstantFeedbackControl hS B G z u -
      z.2 • controlFeedback S B G z (coupledConstantFeedbackControl hS B G z u) =
        B.JInverse z (coupledConstantControlRestriction hS B u) :=
    coupledControlInverse_right B G z hsmall
      (B.JInverse z (coupledConstantControlRestriction hS B u))
  exact (congrArg (fun v : CoupledConstantCircle hS => coupledConstantControlRestriction hS B v)
    (coupledConstantFeedbackInverse_apply hS B G z u)).trans
      (coupled_feedback_restriction_of_equation (coupledConstantControlRestriction hS B).toLinearMap
        (B.JInverse z).toLinearMap (coupledControlCircleInverse hS B z)
        (coupledConstantHeightResponse hS B G z) (controlFeedback S B G z) z.2 hinv
        (coupledConstantHeightResponse_preconditioned hS B G z hrestriction)
        u (coupledConstantFeedbackControl hS B G z u) hN)

variable (hH : ∀ m, 0 < T.H (T.sample m))

include hrestriction hcolumn hdiag hJ hlo hsmall hH in
theorem coupledConstantFeedbackInverse_left (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackInverse hS B G z (coupledConstantFeedbackOperator hS B G z u) = u := by
  exact coupled_feedback_left_of_formulas
    (coupledControlCircleOperator hS B z) (coupledControlCircleInverse hS B z)
    (coupledConstantFeedbackOperator hS B G z) (coupledConstantFeedbackInverse hS B G z)
    (coupledConstantHeightResponse hS B G z) (coupledConstantControlRestriction hS B)
    (coupledConstantFeedbackControl hS B G z)
    (coupledConstantFeedbackOperator_apply hS B G z) (coupledConstantFeedbackInverse_apply hS B G z)
    (coupledConstantFeedbackControl_operator hS B G z hrestriction hcolumn hJ hsmall)
    (coupledControlCircleInverse_left hS B z hrestriction hH hcolumn hdiag hJ hlo) u

include hrestriction hcolumn hdiag hJ hlo hsmall hH in
theorem coupledConstantFeedbackInverse_right (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackOperator hS B G z (coupledConstantFeedbackInverse hS B G z u) = u := by
  exact coupled_feedback_right_of_formulas
    (coupledControlCircleOperator hS B z) (coupledControlCircleInverse hS B z)
    (coupledConstantFeedbackOperator hS B G z) (coupledConstantFeedbackInverse hS B G z)
    (coupledConstantHeightResponse hS B G z) (coupledConstantControlRestriction hS B)
    (coupledConstantFeedbackControl hS B G z)
    (coupledConstantFeedbackOperator_apply hS B G z) (coupledConstantFeedbackInverse_apply hS B G z)
    (coupledConstantFeedbackInverse_restriction hS B G z hrestriction hdiag hJ hlo hsmall)
    (coupledControlCircleInverse_right hS B z hrestriction hH hcolumn hdiag hJ hlo) u

/-- The simple recovery bound used for the all-order tame estimate. -/
theorem coupledConstantFeedbackInverse_grading_le (n : ℕ) (u : CoupledConstantCircle hS) :
    coupledConstantCircleGrading hS n (coupledConstantFeedbackInverse hS B G z u) ≤
      2 * coupledConstantCircleGrading hS n u +
        2 * coupledConstantCircleGrading hS n
          (coupledConstantHeightResponse hS B G z (coupledConstantFeedbackControl hS B G z u)) := by
  exact (congrArg (coupledConstantCircleGrading hS n)
    (coupledConstantFeedbackInverse_apply hS B G z u)).trans_le
      (coupled_feedback_grading_add_bound (coupledConstantCircleGrading hS n)
        (coupledControlCircleInverse hS B z) (coupledControlCircleInverse_grading_le hS B z n)
        u (coupledConstantHeightResponse hS B G z (coupledConstantFeedbackControl hS B G z u)))

include hdiag hJ hlo hsmall in
theorem coupledConstantFeedbackControl_norm_le (u : CoupledConstantCircle hS) :
    ‖coupledConstantFeedbackControl hS B G z u‖ ≤
      4 * ‖coupledConstantControlRestriction hS B u‖ := by
  exact (congrArg norm (coupledConstantFeedbackControl_apply hS B G z u)).trans_le
    (coupled_feedback_two_operator_bound ((coupledControlInverse S B G).inverse z)
      (B.JInverse z) (coupledControlInverse_norm_le_two B G z hsmall)
      (controlJInverse_norm_le_two B z hdiag (fun v => (hJ v).2) hlo)
      (coupledConstantControlRestriction hS B u))

end ContinuousFlexibility.Statements
