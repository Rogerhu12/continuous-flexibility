import ContinuousFlexibility.Analysis.CoupledConstantFeedbackInverse
import ContinuousFlexibility.Analysis.CoupledRegularizingEstimates

/-!
# Smooth tame recovery of the constant control

The Banach Neumann estimate is used only at its fixed base norm. Higher
orders come from the smoothing response in the recovery equation. Its
resulting tame estimate and the two actual inverse identities give joint
continuity and the full Hamilton inverse-family conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {T : MaterialData} {S : PhysicalSpacesData}
  (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
  (B : ControlColumnData S) (G : ScalarInverseData S)

theorem coupledConstantHeightResponse_grading_le (z : AnnularState S × ℝ)
    (s : ℕ) (u : ControlBanach) :
    coupledConstantCircleGrading hS s (coupledConstantHeightResponse hS B G z u) ≤
      (S.circle (3 / 4 : ℝ)).grading s
        (z.2 • B.heightRow z (controlHeightResponse S B G z u)) := by
  rw [coupledConstantHeightResponse_apply]
  exact circleAngularMeanLinear_grading_le hS s _

section Parameters

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  (z : X → AnnularState S × ℝ) (p : ℕ → Seminorm ℝ X) (U : Set X)
  (hdiag : ∀ x ∈ U, ∀ u m, B.J (z x) u m = B.diagonal (z x) m * u m)
  (hJ : ∀ x ∈ U, ∀ u,
    B.JInverse (z x) (B.J (z x) u) = u ∧ B.J (z x) (B.JInverse (z x) u) = u)
  (hlo : ∀ x ∈ U, ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal (z x) m|)
  (hsmall : ∀ x ∈ U, ‖(z x).2 • controlFeedback S B G (z x)‖ < (1 / 2 : ℝ))
  {loss b : ℕ}
  (hregular : ∀ s, b ≤ s → ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ U, ∀ u : ControlBanach,
    (S.circle (3 / 4 : ℝ)).grading s
      ((z x).2 • B.heightRow (z x) (controlHeightResponse S B G (z x) u)) ≤
      c * (1 + p (s + loss) x) * ‖u‖)

include hdiag hJ hlo hsmall hregular

theorem coupledConstantFeedbackInverse_linearFamilyTame :
    LinearFamilyTame p (coupledConstantCircleGrading hS)
      (coupledConstantCircleGrading hS) U
      (fun x => (coupledConstantFeedbackInverse hS B G (z x)).toLinearMap) := by
  obtain ⟨b0, c0, hc0⟩ := controlRestriction_grading_bound B
  apply coupled_inverseFamily_tame_of_regularizing_recovery
    (coupledConstantCircleGrading_monotone hS)
    (control := fun x u => coupledConstantFeedbackControl hS B G (z x) u)
    (response := fun x u => coupledConstantHeightResponse hS B G (z x) u)
    (b := b) (b0 := b0) (loss := loss) (K := 4 * (c0 : ℝ))
    (mul_nonneg (by norm_num) c0.coe_nonneg)
  · intro x hx u
    calc
      ‖coupledConstantFeedbackControl hS B G (z x) u‖ ≤
          4 * ‖coupledConstantControlRestriction hS B u‖ :=
        coupledConstantFeedbackControl_norm_le hS B G (z x)
          (hdiag x hx) (hJ x hx) (hlo x hx) (hsmall x hx) u
      _ ≤ 4 * ((c0 : ℝ) * (S.circle (3 / 4 : ℝ)).grading b0 u.val) := by
        rw [coupledConstantControlRestriction_apply]
        exact mul_le_mul_of_nonneg_left (hc0 u.val) (by norm_num)
      _ = (4 * (c0 : ℝ)) * coupledConstantCircleGrading hS b0 u := by ring
  · intro x _ u s
    exact coupledConstantFeedbackInverse_grading_le hS B G (z x) s u
  · intro s hs
    obtain ⟨c, hc, h⟩ := hregular s hs
    exact ⟨c, hc, fun x hx u =>
      (coupledConstantHeightResponse_grading_le hS B G (z x) s u).trans (h x hx u)⟩

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The regularizing recovery estimate verifies the remaining hypothesis
of the inverse-family theorem on the original closed constant-circle space. -/
theorem coupledConstantFeedbackInverse_smoothTameOn
    (hp : Monotone p) (htp : WithSeminorms p) (hU : IsOpen U)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    (hcolumn : ∀ x ∈ U, ∀ u,
      B.restriction (B.circleColumn (z x) u) = B.J (z x) (B.restriction u))
    (hforward : SmoothTameOn (pairGrading p (coupledConstantCircleGrading hS))
      (coupledConstantCircleGrading hS) (U ×ˢ univ)
      (fun v : X × CoupledConstantCircle hS =>
        coupledConstantFeedbackOperator hS B G (z v.1) v.2)) :
    SmoothTameOn (pairGrading p (coupledConstantCircleGrading hS))
      (coupledConstantCircleGrading hS) (U ×ˢ univ)
      (fun v : X × CoupledConstantCircle hS =>
        coupledConstantFeedbackInverse hS B G (z v.1) v.2) := by
  exact coupled_smoothTameOn_inverseFamily_of_tame hp
    (coupledConstantCircleGrading_monotone hS) (coupledConstantCircleGrading_monotone hS)
    htp (coupledConstantCircleGrading_withSeminorms hS)
    (coupledConstantCircleGrading_withSeminorms hS) hU
    (fun x => coupledConstantFeedbackOperator hS B G (z x))
    (fun x => (coupledConstantFeedbackInverse hS B G (z x)).toLinearMap) hforward
    (fun x hx u => coupledConstantFeedbackInverse_left hS B G (z x)
      hrestriction (hcolumn x hx) (hdiag x hx) (hJ x hx) (hlo x hx) (hsmall x hx) hH u)
    (fun x hx u => coupledConstantFeedbackInverse_right hS B G (z x)
      hrestriction (hcolumn x hx) (hdiag x hx) (hJ x hx) (hlo x hx) (hsmall x hx) hH u)
    (coupledConstantFeedbackInverse_linearFamilyTame hS B G z p U
      hdiag hJ hlo hsmall hregular)

end Parameters

end ContinuousFlexibility.Statements
