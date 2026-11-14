module

public import ContinuousFlexibility.Analysis.PointwiseJacobianMaterialJets

/-!
# Jacobian material jets from positive chart jets

Centering the actual chart at the evaluation point removes its zeroth
value. Its derivative, and hence its actual Jacobian, are unchanged.
Thus the existing pointwise Jacobian estimate needs no bound on the
value of an angular lift and no global smooth extension of the chart.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem planeJacobian_positiveJets_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ F : PolarPoint → PolarPoint, ∀ x : PolarPoint,
      ContDiffAt ℝ ∞ F x →
      (∀ n : ℕ, 0 < n → ‖iteratedFDeriv ℝ n F x‖ ≤
        A n * (1 + p (n + inputLoss) z)) →
      PointwiseMaterialJetBound p loss B z (planeJacobian F) x := by
  obtain ⟨base, loss, hJac⟩ := planeJacobian_fixed_loss_material_bound hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA
  obtain ⟨B, hB, hbound⟩ := hJac A hA
  refine ⟨B, hB, ?_⟩
  intro z hz F x hF hjet
  let Fc : PolarPoint → PolarPoint := fun y => F y - F x
  have hFc : ContDiffAt ℝ ∞ Fc x := hF.sub contDiffAt_const
  have hcentered : PointwiseMaterialJetBound p inputLoss A z Fc x := by
    intro n
    cases n with
    | zero =>
      simpa only [norm_iteratedFDeriv_zero, Fc, sub_self, norm_zero] using
        mul_nonneg (hA 0).le (add_nonneg zero_le_one (apply_nonneg (p (0 + inputLoss)) z))
    | succ n =>
      change ‖iteratedFDeriv ℝ (n + 1) (F - fun _ => F x) x‖ ≤ _
      rw [iteratedFDeriv_sub_apply
        (hF.of_le (by simp : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞)) contDiffAt_const]
      simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero] using
        hjet (n + 1) (Nat.succ_pos n)
  have hJ : planeJacobian Fc = planeJacobian F := by
    funext y
    have hd : fderiv ℝ Fc y = fderiv ℝ F y := fderiv_sub_const (F x)
    simp only [planeJacobian, hd]
  rw [← hJ]
  exact hbound z hz Fc x hFc hcentered

end ContinuousFlexibility.Analysis
