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

variable {T : MaterialData} {S : PhysicalSpacesData}
variable (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
  (B : ControlColumnData S) (G : ScalarInverseData S) (z : AnnularState S × ℝ)

def coupledConstantControlRestriction :
    CoupledConstantCircle hS →L[ℝ] ControlBanach :=
  B.restriction.comp (coupledConstantCircleSubmodule hS).subtypeL

theorem coupledConstantControlRestriction_apply (u : CoupledConstantCircle hS) :
    coupledConstantControlRestriction hS B u = B.restriction u.val := by
  rw [coupledConstantControlRestriction, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]

/-- The mean of the actual scaled height response, with its smooth
constant-circle codomain. -/
def coupledConstantHeightResponse : ControlBanach →L[ℝ] CoupledConstantCircle hS :=
  (coupledConstantCircleProjection hS).comp
    ((z.2 • B.heightRow z).comp (controlHeightResponse S B G z))

theorem coupledConstantHeightResponse_apply (u : ControlBanach) :
    coupledConstantHeightResponse hS B G z u =
      coupledConstantCircleProjection hS
        (z.2 • B.heightRow z (controlHeightResponse S B G z u)) := by
  rw [coupledConstantHeightResponse, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]

def coupledConstantFeedbackOperator :
    CoupledConstantCircle hS →L[ℝ] CoupledConstantCircle hS :=
  coupledControlCircleOperator hS B z -
    (coupledConstantHeightResponse hS B G z).comp (coupledConstantControlRestriction hS B)

theorem coupledConstantFeedbackOperator_apply (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackOperator hS B G z u = coupledControlCircleOperator hS B z u -
      coupledConstantHeightResponse hS B G z (coupledConstantControlRestriction hS B u) := by
  rw [coupledConstantFeedbackOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]

/-- The Banach mean of the recovered inverse. -/
def coupledConstantFeedbackControl : CoupledConstantCircle hS →L[ℝ] ControlBanach :=
  ((coupledControlInverse S B G).inverse z).comp
    ((B.JInverse z).comp (coupledConstantControlRestriction hS B))

theorem coupledConstantFeedbackControl_apply (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackControl hS B G z u = (coupledControlInverse S B G).inverse z
      (B.JInverse z (coupledConstantControlRestriction hS B u)) := by
  rw [coupledConstantFeedbackControl, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]

/-- Recovery in the actual constant-circle space after the base-space
Neumann solve. All maps are total; the identities below specify the domain. -/
def coupledConstantFeedbackInverse :
    CoupledConstantCircle hS →L[ℝ] CoupledConstantCircle hS :=
  (coupledControlCircleInverse hS B z).comp
    (ContinuousLinearMap.id ℝ (CoupledConstantCircle hS) +
      (coupledConstantHeightResponse hS B G z).comp (coupledConstantFeedbackControl hS B G z))

theorem coupledConstantFeedbackInverse_apply (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackInverse hS B G z u = coupledControlCircleInverse hS B z
      (u + coupledConstantHeightResponse hS B G z (coupledConstantFeedbackControl hS B G z u)) := by
  rw [coupledConstantFeedbackInverse, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]

variable
  (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
    angularMean ((S.circle (3 / 4 : ℝ)).decode u m))

theorem coupledConstantControlRestriction_projection (u : CircleSpace S) :
    coupledConstantControlRestriction hS B (coupledConstantCircleProjection hS u) =
      B.restriction u := by
  rw [coupledConstantControlRestriction_apply, coupledConstantCircleProjection_val,
    controlRestriction_angularMeanProjection hS B hrestriction]

theorem coupledConstantHeightResponse_restriction (u : ControlBanach) :
    coupledConstantControlRestriction hS B (coupledConstantHeightResponse hS B G z u) =
      z.2 • controlMeanRow S B z (controlHeightResponse S B G z u) := by
  rw [coupledConstantHeightResponse_apply,
    coupledConstantControlRestriction_projection hS B hrestriction,
    map_smul, controlMeanRow_apply]

variable
  (hcolumn : ∀ u, B.restriction (B.circleColumn z u) = B.J z (B.restriction u))
  (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
  (hJ : ∀ u, B.JInverse z (B.J z u) = u ∧ B.J z (B.JInverse z u) = u)
  (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|)
  (hsmall : ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ))

theorem coupledConstantFeedbackOperator_preconditioned_restriction
    (u : CoupledConstantCircle hS) :
    B.JInverse z (coupledConstantControlRestriction hS B
      (coupledConstantFeedbackOperator hS B G z u)) =
      coupledConstantControlRestriction hS B u - z.2 • controlFeedback S B G z
        (coupledConstantControlRestriction hS B u) := by
  have hforward : coupledConstantControlRestriction hS B (coupledControlCircleOperator hS B z u) =
      B.J z (coupledConstantControlRestriction hS B u) := by
    simpa only [coupledConstantControlRestriction_apply] using
      coupledControlCircleOperator_restriction hS B z hrestriction hcolumn u
  rw [coupledConstantFeedbackOperator_apply, map_sub, hforward,
    coupledConstantHeightResponse_restriction hS B G z hrestriction,
    map_sub, map_smul, (hJ _).1, controlFeedback_apply]

theorem coupledConstantFeedbackControl_operator (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackControl hS B G z (coupledConstantFeedbackOperator hS B G z u) =
      coupledConstantControlRestriction hS B u := by
  rw [coupledConstantFeedbackControl_apply,
    coupledConstantFeedbackOperator_preconditioned_restriction hS B G z hrestriction hcolumn hJ]
  exact coupledControlInverse_left B G z hsmall _

/-- The circle recovery has exactly the same mean as the Banach solution. -/
theorem coupledConstantFeedbackInverse_restriction (u : CoupledConstantCircle hS) :
    coupledConstantControlRestriction hS B (coupledConstantFeedbackInverse hS B G z u) =
      coupledConstantFeedbackControl hS B G z u := by
  have hinv (v : CoupledConstantCircle hS) :
      coupledConstantControlRestriction hS B (coupledControlCircleInverse hS B z v) =
        B.JInverse z (coupledConstantControlRestriction hS B v) := by
    simpa only [coupledConstantControlRestriction_apply] using
      coupledControlCircleInverse_restriction hS B z hrestriction hdiag (fun v => (hJ v).2) hlo v
  rw [coupledConstantFeedbackInverse_apply, hinv, map_add,
    coupledConstantHeightResponse_restriction hS B G z hrestriction,
    map_add, map_smul, ← controlFeedback_apply]
  have hN := coupledControlInverse_right B G z hsmall
    (B.JInverse z (coupledConstantControlRestriction hS B u))
  rw [← coupledConstantFeedbackControl_apply hS B G z u] at hN
  exact (sub_eq_iff_eq_add.mp hN).symm

variable (hH : ∀ m, 0 < T.H (T.sample m))

theorem coupledConstantFeedbackInverse_left (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackInverse hS B G z (coupledConstantFeedbackOperator hS B G z u) = u := by
  rw [coupledConstantFeedbackInverse_apply,
    coupledConstantFeedbackControl_operator hS B G z hrestriction hcolumn hJ hsmall,
    coupledConstantFeedbackOperator_apply, sub_add_cancel]
  exact coupledControlCircleInverse_left hS B z hrestriction hH hcolumn hdiag hJ hlo u

theorem coupledConstantFeedbackInverse_right (u : CoupledConstantCircle hS) :
    coupledConstantFeedbackOperator hS B G z (coupledConstantFeedbackInverse hS B G z u) = u := by
  rw [coupledConstantFeedbackOperator_apply,
    coupledConstantFeedbackInverse_restriction hS B G z hrestriction hdiag hJ hlo hsmall,
    coupledConstantFeedbackInverse_apply,
    coupledControlCircleInverse_right hS B z hrestriction hH hcolumn hdiag hJ hlo,
    add_sub_cancel_right]

/-- The simple recovery bound used for the all-order tame estimate. -/
theorem coupledConstantFeedbackInverse_grading_le (n : ℕ) (u : CoupledConstantCircle hS) :
    coupledConstantCircleGrading hS n (coupledConstantFeedbackInverse hS B G z u) ≤
      2 * coupledConstantCircleGrading hS n u +
        2 * coupledConstantCircleGrading hS n
          (coupledConstantHeightResponse hS B G z (coupledConstantFeedbackControl hS B G z u)) := by
  rw [coupledConstantFeedbackInverse_apply]
  calc
    _ ≤ 2 * coupledConstantCircleGrading hS n
        (u + coupledConstantHeightResponse hS B G z (coupledConstantFeedbackControl hS B G z u)) :=
      coupledControlCircleInverse_grading_le hS B z n _
    _ ≤ 2 * (coupledConstantCircleGrading hS n u +
        coupledConstantCircleGrading hS n
          (coupledConstantHeightResponse hS B G z (coupledConstantFeedbackControl hS B G z u))) :=
      mul_le_mul_of_nonneg_left (map_add_le_add _ _ _) (by norm_num)
    _ = _ := by ring

theorem coupledConstantFeedbackControl_norm_le (u : CoupledConstantCircle hS) :
    ‖coupledConstantFeedbackControl hS B G z u‖ ≤
      4 * ‖coupledConstantControlRestriction hS B u‖ := by
  have hJnorm := controlJInverse_norm_le_two B z hdiag (fun v => (hJ v).2) hlo
  have hNnorm := coupledControlInverse_norm_le_two B G z hsmall
  rw [coupledConstantFeedbackControl_apply]
  calc
    _ ≤ ‖(coupledControlInverse S B G).inverse z‖ *
        ‖B.JInverse z (coupledConstantControlRestriction hS B u)‖ :=
      ((coupledControlInverse S B G).inverse z).le_opNorm _
    _ ≤ 2 * ‖B.JInverse z (coupledConstantControlRestriction hS B u)‖ :=
      mul_le_mul_of_nonneg_right hNnorm (norm_nonneg _)
    _ ≤ 2 * (2 * ‖coupledConstantControlRestriction hS B u‖) :=
      mul_le_mul_of_nonneg_left
        (((B.JInverse z).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hJnorm (norm_nonneg _))) (by norm_num)
    _ = _ := by ring

end ContinuousFlexibility.Statements
