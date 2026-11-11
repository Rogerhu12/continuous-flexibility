import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations
import ContinuousFlexibility.Analysis.RootAngularProduct

/-!
# Actual jets of the smooth root angular denominator

The denominator is φθ² − x³χθ². Differentiating the original fields
once and applying two genuine product estimates proves its fixed-loss
bound. The fixed radial cubic has state-independent jets at every root
point, including all angular representatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private def rootRadialCubeJetConstant (n : ℕ) : ℝ :=
  1 + ‖iteratedFDeriv ℝ n (fun y : PolarPoint => y.1 ^ 3) (0, 0)‖

private theorem rootRadialCubeJetConstant_pos (n : ℕ) :
    0 < rootRadialCubeJetConstant n :=
  add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)

private theorem rootRadialCube_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (z : E) (θ : ℝ) :
    PointwiseMaterialJetBound p loss rootRadialCubeJetConstant z
      (fun y : PolarPoint => y.1 ^ 3) (0, θ) := by
  intro n
  have he : (fun y : PolarPoint => ((0, θ) + y).1 ^ 3) =
      (fun y : PolarPoint => y.1 ^ 3) := by
    funext y
    change ((0 : ℝ) + y.1) ^ 3 = y.1 ^ 3
    rw [zero_add]
  have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun y : PolarPoint => y.1 ^ 3) n (0, θ) (0, 0)
  rw [he] at ht
  have hj : iteratedFDeriv ℝ n (fun y : PolarPoint => y.1 ^ 3) (0, θ) =
      iteratedFDeriv ℝ n (fun y : PolarPoint => y.1 ^ 3) (0, 0) := by
    simpa only [Prod.mk_add_mk, zero_add, add_zero] using ht.symm
  rw [hj]
  exact (le_add_of_nonneg_left zero_le_one).trans
    (le_mul_of_one_le_right (rootRadialCubeJetConstant_pos n).le
      (le_add_of_nonneg_right (apply_nonneg _ _)))

theorem rootAngularProduct_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ G : ℝ × ℝ × ℝ → ℝ, ∀ θ : ℝ,
      ContDiffAt ℝ ∞ (extendedRootEven G) (0, θ) →
      ContDiffAt ℝ ∞ (extendedRootOddCoefficient G) (0, θ) →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootEven G) (0, θ) →
      PointwiseMaterialJetBound p inputLoss A z (extendedRootOddCoefficient G) (0, θ) →
      PointwiseMaterialJetBound p loss B z (rootAngularProduct G) (0, θ) := by
  obtain ⟨squareBase, squareLoss, hsquare⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := PolarPoint) hp hI (inputLoss + 1)
  obtain ⟨cubeBase, cubeLoss, hcube⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := PolarPoint) hp hI squareLoss
  refine ⟨max squareBase cubeBase, max squareLoss cubeLoss, ?_⟩
  intro A hA
  obtain ⟨D, hD, hsquares⟩ := hsquare (fun n => A (n + 1)) (fun n => hA (n + 1))
  let P : ℕ → ℝ := fun n => D n + rootRadialCubeJetConstant n
  have hP (n : ℕ) : 0 < P n := add_pos (hD n) (rootRadialCubeJetConstant_pos n)
  obtain ⟨Q, hQ, hcubes⟩ := hcube P hP
  refine ⟨fun n => D n + Q n, fun n => add_pos (hD n) (hQ n), ?_⟩
  intro z hz G θ hφ hχ hφjet hχjet
  have hzSquare : p squareBase z ≤ 1 := ((hp (le_max_left _ _)) z).trans hz
  have hzCube : p cubeBase z ≤ 1 := ((hp (le_max_right _ _)) z).trans hz
  have hdφ : ContDiffAt ℝ ∞ (angularPartial (extendedRootEven G)) (0, θ) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hdχ : ContDiffAt ℝ ∞ (angularPartial (extendedRootOddCoefficient G)) (0, θ) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hdφjet : PointwiseMaterialJetBound p (inputLoss + 1) (fun n => A (n + 1)) z
      (angularPartial (extendedRootEven G)) (0, θ) :=
    hφjet.directionalPartial hφ (0, 1) (by simp)
  have hdχjet : PointwiseMaterialJetBound p (inputLoss + 1) (fun n => A (n + 1)) z
      (angularPartial (extendedRootOddCoefficient G)) (0, θ) :=
    hχjet.directionalPartial hχ (0, 1) (by simp)
  have hφsq : PointwiseMaterialJetBound p squareLoss D z
      (fun y => angularPartial (extendedRootEven G) y ^ 2) (0, θ) := by
    simpa only [PointwiseMaterialJetBound, pow_two] using
      hsquares z hzSquare _ _ (0, θ) hdφ hdφ hdφjet hdφjet
  have hχsq : PointwiseMaterialJetBound p squareLoss D z
      (fun y => angularPartial (extendedRootOddCoefficient G) y ^ 2) (0, θ) := by
    simpa only [PointwiseMaterialJetBound, pow_two] using
      hsquares z hzSquare _ _ (0, θ) hdχ hdχ hdχjet hdχjet
  have hχsqP := hχsq.mono hp le_rfl (fun n => (hD n).le)
    (fun n => le_add_of_nonneg_right (rootRadialCubeJetConstant_pos n).le)
  have hcubeP := (rootRadialCube_material_bound p squareLoss z θ).mono hp le_rfl
    (fun n => (rootRadialCubeJetConstant_pos n).le)
    (fun n => le_add_of_nonneg_left (hD n).le)
  have hsecond : PointwiseMaterialJetBound p cubeLoss Q z
      (fun y => y.1 ^ 3 * angularPartial (extendedRootOddCoefficient G) y ^ 2) (0, θ) :=
    hcubes z hzCube _ _ (0, θ) (contDiffAt_fst.pow 3) (hdχ.pow 2) hcubeP hχsqP
  have hfirst' := hφsq.mono hp (le_max_left squareLoss cubeLoss)
    (fun n => (hD n).le) (fun _ => le_rfl)
  have hsecond' := hsecond.mono hp (le_max_right squareLoss cubeLoss)
    (fun n => (hQ n).le) (fun _ => le_rfl)
  exact hfirst'.sub (hdφ.pow 2) ((contDiffAt_fst.pow 3).mul (hdχ.pow 2)) hsecond'

end ContinuousFlexibility.Analysis
