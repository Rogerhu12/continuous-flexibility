import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds
import ContinuousFlexibility.Analysis.FlowJetLinearization

/-!
# Fixed-loss jets of actual circle-lift compositions

An angular normalization is measured by its displacement from the identity.
The inner map is measured by its displacement from a fixed linear angular
projection. The actual composition has the same form. The partition
estimate and interpolation preserve one high state factor at every order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem positiveJet_le_linearDisplacement
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {g : X → ℝ} (hg : ContDiff ℝ ∞ g) (L : X →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (x : X) :
    ‖iteratedFDeriv ℝ n g x‖ ≤
      ‖iteratedFDeriv ℝ n (fun y => g y - L y) x‖ + 1 := by
  have he : g = (fun y => g y - L y) + (L : X → ℝ) := by
    funext y
    simp only [Pi.add_apply, sub_add_cancel]
  have hjet : iteratedFDeriv ℝ n g x =
      iteratedFDeriv ℝ n (fun y => g y - L y) x +
        iteratedFDeriv ℝ n (L : X → ℝ) x := by
    conv_lhs => rw [he]
    exact iteratedFDeriv_add_apply
      ((hg.sub L.contDiff).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) L.contDiff.contDiffAt
  rw [hjet]
  exact (norm_add_le _ _).trans
    (add_le_add le_rfl ((flowJet_norm_iteratedFDeriv_clm_le L hn x).trans hL))

/-- This estimate uses actual derivatives of the normalization and the
inner displacement. The low order and loss are chosen before all their
numerical majorants, functions, and evaluation points. -/
theorem circleLiftComposition_displacement_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 →
      ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h →
      ∀ g : X → ℝ, ContDiff ℝ ∞ g →
      ∀ L : X →L[ℝ] ℝ, ‖L‖ ≤ 1 → ∀ x : X,
      (∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun θ => h θ - θ) (g x)‖ ≤
        A n * (1 + p (n + inputLoss) z)) →
      (∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun y => g y - L y) x‖ ≤
        A n * (1 + p (n + inputLoss) z)) →
      ∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun y => h (g y) - L y) x‖ ≤
        B n * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, hcomp⟩ :=
    coordinateComposition_fixed_loss_material_bound (X := X) (Y := ℝ) (Z := ℝ)
      hp hI inputLoss
  refine ⟨base, max loss inputLoss, ?_⟩
  intro A hA
  let A' : ℕ → ℝ := fun n => 1 + A n
  have hA' (n : ℕ) : 1 ≤ A' n := le_add_of_nonneg_right (hA n).le
  obtain ⟨C, hC, hbound⟩ := hcomp A' hA'
  let B : ℕ → ℝ := fun n => match n with
    | 0 => 2 * A 0
    | k + 1 => C k + A (k + 1)
  have hB (n : ℕ) : 0 < B n := by
    cases n with
    | zero => exact mul_pos (by norm_num) (hA 0)
    | succ n => exact add_pos (hC n) (hA (n + 1))
  refine ⟨B, hB, ?_⟩
  intro z hz h hh g hg L hL x houter hinner n
  let f : ℝ → ℝ := fun θ => h θ - θ
  let u : X → ℝ := fun y => g y - L y
  have hf : ContDiff ℝ ∞ f := hh.sub contDiff_id
  have hu : ContDiff ℝ ∞ u := hg.sub L.contDiff
  have he : (fun y => h (g y) - L y) = (f ∘ g) + u := by
    funext y
    simp only [Pi.add_apply, Function.comp_apply, f, u]
    ring
  have hgrade (k : ℕ) :
      1 + p (k + inputLoss) z ≤ 1 + p (k + max loss inputLoss) z :=
    add_le_add (le_refl (1 : ℝ))
      ((hp (Nat.add_le_add_left (le_max_right loss inputLoss) k)) z)
  cases n with
  | zero =>
      have hout : ‖f (g x)‖ ≤ A 0 * (1 + p inputLoss z) := by
        simpa only [norm_iteratedFDeriv_zero, Nat.zero_add] using houter 0
      have hin : ‖u x‖ ≤ A 0 * (1 + p inputLoss z) := by
        simpa only [norm_iteratedFDeriv_zero, Nat.zero_add] using hinner 0
      rw [he, norm_iteratedFDeriv_zero, Pi.add_apply, Function.comp_apply]
      apply (norm_add_le _ _).trans
      apply (add_le_add hout hin).trans
      have hg0 := mul_le_mul_of_nonneg_left (hgrade 0) (mul_nonneg (by norm_num) (hA 0).le)
      simpa only [B, Nat.zero_add, two_mul, add_mul] using hg0
  | succ n =>
      have hfb (k : ℕ) (_ : 1 ≤ k) :
          ‖iteratedFDeriv ℝ k f (g x)‖ ≤
            A' k * (1 : ℝ) ^ A' k * (1 + p (k + inputLoss) z) := by
        simp only [Real.one_rpow, mul_one]
        exact (houter k).trans (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one)
          (add_nonneg zero_le_one (apply_nonneg _ _)))
      have hgb (k : ℕ) (hk : 1 ≤ k) :
          ‖iteratedFDeriv ℝ k g x‖ ≤
            A' k * (1 : ℝ) ^ A' k * (1 + p (k + inputLoss) z) := by
        simp only [Real.one_rpow, mul_one]
        apply (positiveJet_le_linearDisplacement hg L hL hk x).trans
        apply (add_le_add (hinner k) le_rfl).trans
        dsimp only [A']
        nlinarith [apply_nonneg (p (k + inputLoss)) z]
      have hfg : ‖iteratedFDeriv ℝ (n + 1) (f ∘ g) x‖ ≤
          C n * (1 + p ((n + 1) + loss) z) := by
        simpa only [Real.one_rpow, mul_one] using
          hbound z hz 1 le_rfl f g x hf.contDiffAt hg.contDiffAt hfb hgb n
      have hfg' := hfg.trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (1 : ℝ))
          ((hp (Nat.add_le_add_left (le_max_left loss inputLoss) (n + 1))) z)) (hC n).le)
      have hu' := (hinner (n + 1)).trans
        (mul_le_mul_of_nonneg_left (hgrade (n + 1)) (hA (n + 1)).le)
      rw [he, iteratedFDeriv_add_apply
        ((hf.comp hg).contDiffAt.of_le (by simp : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞))
        (hu.contDiffAt.of_le (by simp : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞))]
      apply (norm_add_le _ _).trans
      exact (add_le_add hfg' hu').trans_eq (by dsimp only [B]; ring)

end ContinuousFlexibility.Analysis
