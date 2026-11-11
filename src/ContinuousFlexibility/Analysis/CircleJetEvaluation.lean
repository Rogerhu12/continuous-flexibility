import ContinuousFlexibility.Analysis.CircleAngleEvaluation

open Set Filter MeasureTheory
open scoped ContDiff ENNReal RealInnerProductSpace Topology

namespace ContinuousFlexibility.Statements

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem periodic_iteratedDeriv_angle {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g Real.pi) (b : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv b g) ∧ Function.Periodic (iteratedDeriv b g) Real.pi := by
  induction b with
  | zero => simpa only [iteratedDeriv_zero] using And.intro hg hp
  | succ b ih =>
    rw [iteratedDeriv_succ]
    refine ⟨(contDiff_infty_iff_deriv.mp ih.1).2, ?_⟩
    intro x
    let G := iteratedDeriv b g
    have h₁ : HasDerivAt (fun t : ℝ => t + Real.pi) 1 x :=
      (hasDerivAt_id x).add_const Real.pi
    have h₂ := ((ih.1.differentiable (by simp) (x + Real.pi)).hasDerivAt).comp x h₁
    have he : (G ∘ fun t : ℝ => t + Real.pi) = G := funext ih.2
    change HasDerivAt (G ∘ fun t : ℝ => t + Real.pi) (deriv G (x + Real.pi) * 1) x at h₂
    rw [he, mul_one] at h₂
    exact h₂.deriv.symm

variable (T : MaterialData) (hM : ∀ m, 0 < T.M (T.sample m))

private def circleJetAngularLevel (m b : ℕ) : circleJetClosedSubmodule T b →L[ℝ] AngleL2 :=
  (circleJetCoordinate b m (circleJetPureAngularIndex b)).comp (circleJetClosedSubmodule T b).subtypeL

private theorem circleJetAngularLevel_norm_le (m b : ℕ) (z : circleJetClosedSubmodule T b) :
    ‖circleJetAngularLevel T m b z‖ ≤ ‖z‖ :=
  (PiLp.norm_apply_le (z.val m) (circleJetPureAngularIndex b)).trans
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) z.val m)

private def circleJetAngularPairLevel (m b : ℕ) :
    circleJetClosedSubmodule T (b + 1) →L[ℝ] AngleL2 × AngleL2 :=
  ((circleJetAngularLevel T m b).comp (circleJetBond T hM b)).prod
    (circleJetAngularLevel T m (b + 1))

private theorem circleJetAngularPairLevel_norm_le (m b : ℕ)
    (z : circleJetClosedSubmodule T (b + 1)) :
    ‖circleJetAngularPairLevel T hM m b z‖ ≤ ‖z‖ := by
  change ‖(circleJetAngularLevel T m b (circleJetBond T hM b z),
    circleJetAngularLevel T m (b + 1) z)‖ ≤ ‖z‖
  rw [Prod.norm_mk, max_le_iff]
  exact ⟨(circleJetAngularLevel_norm_le T m b (circleJetBond T hM b z)).trans
    (circleJetGraphRestrict_norm_le T hM (Nat.le_succ b) z),
    circleJetAngularLevel_norm_le T m (b + 1) z⟩

/-- Evaluation of the fixed-order decoded derivative factors through level b+1. -/
def circleJetEvaluationLevel (γ : ℝ) (m b : ℕ) (x : ℝ) :
    circleJetClosedSubmodule T (b + 1) →L[ℝ] ℝ :=
  T.H (T.sample m) ^ γ • (anglePairEvaluation (toIocMod Real.pi_pos 0 x)).comp
    (circleJetAngularPairLevel T hM m b)

def circleJetEvaluation (γ : ℝ) (m b : ℕ) (x : ℝ) :
    CircleJetProjectiveLimit T hM →L[ℝ] ℝ :=
  (circleJetEvaluationLevel T hM γ m b x).comp
    (Analysis.projectiveCoordinate (fun s => ↥(circleJetClosedSubmodule T s))
      (circleJetBond T hM) (b + 1))

theorem circleJetEvaluation_apply (γ : ℝ) (m b : ℕ) (x : ℝ)
    (u : CircleJetProjectiveLimit T hM) :
    circleJetEvaluation T hM γ m b x u = iteratedDeriv b (circleJetDecoded u γ m) x := by
  have hraw := circleJetRawSmooth_spec u m
  have hreg := periodic_iteratedDeriv_angle hraw.1 hraw.2.1 b
  have hev := anglePairEvaluation_of_weakDerivative
    (circleJetAngularDerivative_adjacent u m b) hreg.1.continuous hreg.2 (hraw.2.2 b) x
  change T.H (T.sample m) ^ γ * anglePairEvaluation (toIocMod Real.pi_pos 0 x)
    (circleJetAngularLevel T m b (circleJetBond T hM b (u.val (b + 1))),
      circleJetAngularLevel T m (b + 1) (u.val (b + 1))) =
    iteratedDeriv b (fun y => T.H (T.sample m) ^ γ * circleJetRawSmooth u m y) x
  rw [u.property b, iteratedDeriv_const_mul_field]
  exact congrArg (T.H (T.sample m) ^ γ * ·) hev

theorem circleJetEvaluationLevel_norm_le (γ : ℝ) (m b : ℕ) (x : ℝ)
    (z : circleJetClosedSubmodule T (b + 1)) :
    ‖circleJetEvaluationLevel T hM γ m b x z‖ ≤
      (|T.H (T.sample m) ^ γ| * anglePairEvaluationConstant) * ‖z‖ := by
  change ‖T.H (T.sample m) ^ γ * anglePairEvaluation (toIocMod Real.pi_pos 0 x)
    (circleJetAngularPairLevel T hM m b z)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    ((anglePairEvaluation_norm_le _ _).trans
      (mul_le_mul_of_nonneg_left (circleJetAngularPairLevel_norm_le T hM m b z)
        anglePairEvaluationConstant_nonneg)) (abs_nonneg _)

theorem circleJetEvaluationLevel_opNorm_le (γ : ℝ) (m b : ℕ) (x : ℝ) :
    ‖circleJetEvaluationLevel T hM γ m b x‖ ≤
      |T.H (T.sample m) ^ γ| * anglePairEvaluationConstant :=
  (circleJetEvaluationLevel T hM γ m b x).opNorm_le_bound
    (mul_nonneg (abs_nonneg _) anglePairEvaluationConstant_nonneg)
    (circleJetEvaluationLevel_norm_le T hM γ m b x)

theorem circleJetDecoded_iteratedDeriv_abs_le (γ : ℝ) (m b : ℕ) (x : ℝ)
    (u : CircleJetProjectiveLimit T hM) :
    |iteratedDeriv b (circleJetDecoded u γ m) x| ≤
      (|T.H (T.sample m) ^ γ| * anglePairEvaluationConstant) * ‖u.val (b + 1)‖ := by
  rw [← circleJetEvaluation_apply T hM γ m b x u, ← Real.norm_eq_abs]
  exact circleJetEvaluationLevel_norm_le T hM γ m b x (u.val (b + 1))

/-- The same decoded sequence as a continuous linear map into the actual
product of pointwise function spaces. -/
def circleJetDecodeCLM (γ : ℝ) : CircleJetProjectiveLimit T hM →L[ℝ] (ℕ → ℝ → ℝ) :=
  ContinuousLinearMap.pi fun m =>
    ContinuousLinearMap.pi fun x => circleJetEvaluation T hM γ m 0 x

theorem circleJetDecodeCLM_apply (γ : ℝ) (u : CircleJetProjectiveLimit T hM) :
    circleJetDecodeCLM T hM γ u = circleJetDecoded u γ := by
  funext m x
  rw [circleJetDecodeCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.pi_apply,
    circleJetEvaluation_apply, iteratedDeriv_zero]

theorem continuous_circleJetDecoded (γ : ℝ) :
    Continuous (fun u : CircleJetProjectiveLimit T hM => circleJetDecoded u γ) := by
  have h : (fun u : CircleJetProjectiveLimit T hM => circleJetDecoded u γ) =
      circleJetDecodeCLM T hM γ := funext fun u => (circleJetDecodeCLM_apply T hM γ u).symm
  rw [h]
  exact (circleJetDecodeCLM T hM γ).continuous

end

end ContinuousFlexibility.Statements
