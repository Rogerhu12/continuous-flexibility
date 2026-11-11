import ContinuousFlexibility.Analysis.CenteredJacobianMaterialJets
import ContinuousFlexibility.Analysis.AbsoluteReciprocalJetBounds

/-!
# The actual reciprocal Jacobian from pointwise positive chart jets

Only genuine smoothness at the evaluation point is needed. Centering
first obtains the actual Jacobian jets, and the scalar absolute
reciprocal estimate uses the actual lower bound on that determinant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem absolutePlaneJacobian_positiveJets_at_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ κ : ℝ, 0 < κ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p low z ≤ 1 → ∀ F : PolarPoint → PolarPoint, ∀ q : PolarPoint,
        ContDiffAt ℝ ∞ F q → κ ≤ |planeJacobian F q| →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F q‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        PointwiseMaterialJetBound p outLoss B z (fun y => |planeJacobian F y|⁻¹) q := by
  obtain ⟨baseJ, lossJ, hjac⟩ := planeJacobian_positiveJets_fixed_loss_material_bound hp hI inputLoss
  obtain ⟨baseR, lossR, hrec⟩ := absoluteReciprocal_fixed_loss_material_bound hp hI lossJ
  refine ⟨max baseJ baseR, lossR, ?_⟩
  intro A hA κ hκ
  obtain ⟨P, hP, hJbound⟩ := hjac A hA
  let C : ℕ → ℝ := fun n => 1 + P n
  have hC (n : ℕ) : 1 ≤ C n := le_add_of_nonneg_right (hP n).le
  obtain ⟨B, hB, hRbound⟩ := hrec C hC κ hκ
  refine ⟨B, hB, ?_⟩
  intro z hz F q hF hκq hraw
  have hzJ : p baseJ z ≤ 1 := (hp (le_max_left _ _) z).trans hz
  have hzR : p baseR z ≤ 1 := (hp (le_max_right _ _) z).trans hz
  have hJ := hJbound z hzJ F q hF (fun n hn => hraw n hn)
  intro n
  have hh := hRbound z hzR 1 le_rfl (planeJacobian F) q
    (contDiffAt_planeJacobian hF) hκq
    (fun k _ => by
      have hPC : P k ≤ C k := le_add_of_nonneg_left zero_le_one
      have he := (hJ k).trans (mul_le_mul_of_nonneg_right hPC
        (add_nonneg zero_le_one (apply_nonneg _ _)))
      simpa only [Real.one_rpow, mul_one] using he) n
  simpa only [Real.one_rpow, mul_one] using hh

end ContinuousFlexibility.Analysis
