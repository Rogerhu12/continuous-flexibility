import ContinuousFlexibility.Analysis.PositivePowerMaterialJets
import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual Airy coordinate jets on a positive travel interval

The genuine first-integral travel and angle determine the coordinate
map. Away from a root the travel lies in a fixed positive interval, so
the actual two-thirds power is estimated by the existing composition
theorem. Only positive jets of the angular lift enter the map estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem angle_positiveJet_from_displacement
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {z : E}
    {φ : PolarPoint → ℝ} {q : PolarPoint}
    (hφ : ContDiffAt ℝ ∞ φ q)
    (hj : PointwiseMaterialJetBound p loss A z (fun y => φ y - y.2) q)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n φ q‖ ≤ (A n + 1) * (1 + p (n + loss) z) := by
  have he : iteratedFDeriv ℝ n (fun y : PolarPoint => φ y - y.2) q =
      iteratedFDeriv ℝ n φ q - iteratedFDeriv ℝ n (fun y : PolarPoint => y.2) q :=
    iteratedFDeriv_sub_apply (hφ.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) contDiffAt_snd
  have hlinear : ‖iteratedFDeriv ℝ n (fun y : PolarPoint => y.2) q‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.coe_snd'] using
      (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.snd ℝ ℝ ℝ) hn q).trans
        (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  calc
    _ = ‖(iteratedFDeriv ℝ n φ q - iteratedFDeriv ℝ n (fun y : PolarPoint => y.2) q) +
        iteratedFDeriv ℝ n (fun y : PolarPoint => y.2) q‖ := by rw [sub_add_cancel]
    _ ≤ ‖iteratedFDeriv ℝ n (fun y : PolarPoint => φ y - y.2) q‖ +
        ‖iteratedFDeriv ℝ n (fun y : PolarPoint => y.2) q‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ A n * (1 + p (n + loss) z) + 1 := add_le_add (hj n) hlinear
    _ ≤ A n * (1 + p (n + loss) z) + (1 + p (n + loss) z) :=
      add_le_add le_rfl (le_add_of_nonneg_right (apply_nonneg _ _))
    _ = _ := by ring

theorem airyInteriorChart_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ l u : ℝ, 0 < l → l ≤ u →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p low z ≤ 1 → ∀ τ φ : PolarPoint → ℝ, ∀ q : PolarPoint,
        ContDiffAt ℝ ∞ τ q → ContDiffAt ℝ ∞ φ q → τ q ∈ Icc l u →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n τ q‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        PointwiseMaterialJetBound p inputLoss A z (fun y => φ y - y.2) q →
        ContDiffAt ℝ ∞ (fun y => (((3 / 2 : ℝ) * τ y) ^ (2 / 3 : ℝ), φ y)) q ∧
        PointwiseMaterialJetBound p outLoss B z
          (fun y => ((3 / 2 : ℝ) * τ y) ^ (2 / 3 : ℝ)) q ∧
        ∀ n : ℕ, 1 ≤ n →
          ‖iteratedFDeriv ℝ n (fun y => (((3 / 2 : ℝ) * τ y) ^ (2 / 3 : ℝ), φ y)) q‖ ≤
            B n * (1 + p (n + outLoss) z) := by
  obtain ⟨low, powerLoss, hpower⟩ :=
    positivePower_fixed_loss_material_bound (X := PolarPoint) hp hI inputLoss
  refine ⟨low, max inputLoss powerLoss, ?_⟩
  intro A hA l u hl hlu
  let C : ℕ → ℝ := fun n => (3 / 2 : ℝ) * A n
  have hC (n : ℕ) : 0 < C n := mul_pos (by norm_num) (hA n)
  obtain ⟨P, hP, hbound⟩ := hpower C hC ((3 / 2 : ℝ) * l) ((3 / 2 : ℝ) * u)
    (2 / 3 : ℝ) (mul_pos (by norm_num) hl) (mul_le_mul_of_nonneg_left hlu (by norm_num))
  let B : ℕ → ℝ := fun n => P n + A n + 1
  have hB (n : ℕ) : 0 < B n := add_pos (add_pos (hP n) (hA n)) zero_lt_one
  refine ⟨B, hB, ?_⟩
  intro z hz τ φ q hτ hφ hτvalue hτjets hφjets
  have hscaled : ContDiffAt ℝ ∞ (fun y => (3 / 2 : ℝ) * τ y) q := contDiffAt_const.mul hτ
  have hscaledValue : (3 / 2 : ℝ) * τ q ∈ Icc ((3 / 2 : ℝ) * l) ((3 / 2 : ℝ) * u) :=
    ⟨mul_le_mul_of_nonneg_left hτvalue.1 (by norm_num),
      mul_le_mul_of_nonneg_left hτvalue.2 (by norm_num)⟩
  have hscaledJets (n : ℕ) (hn : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n (fun y => (3 / 2 : ℝ) * τ y) q‖ ≤
        C n * (1 + p (n + inputLoss) z) := by
    change ‖iteratedFDeriv ℝ n (fun y => (3 / 2 : ℝ) • τ y) q‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hτ.of_le (by simp : (n : ℕ∞ω) ≤ ∞)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simpa only [C, mul_assoc] using mul_le_mul_of_nonneg_left (hτjets n hn)
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hradial := hbound z hz (fun y => (3 / 2 : ℝ) * τ y) q hscaled hscaledValue hscaledJets
  have hpositive : 0 < (3 / 2 : ℝ) * τ q :=
    mul_pos (by norm_num) (hl.trans_le hτvalue.1)
  have hξ : ContDiffAt ℝ ∞ (fun y => ((3 / 2 : ℝ) * τ y) ^ (2 / 3 : ℝ)) q :=
    hscaled.rpow_const_of_ne hpositive.ne'
  have hradial' : PointwiseMaterialJetBound p (max inputLoss powerLoss) B z
      (fun y => ((3 / 2 : ℝ) * τ y) ^ (2 / 3 : ℝ)) q :=
    PointwiseMaterialJetBound.mono hp (le_max_right _ _) (fun n => (hP n).le)
      (fun n => by dsimp only [B]; linarith [hA n]) hradial
  refine ⟨hξ.prodMk hφ, hradial', ?_⟩
  intro n hn
  have hangle : ‖iteratedFDeriv ℝ n φ q‖ ≤ B n * (1 + p (n + max inputLoss powerLoss) z) :=
    (angle_positiveJet_from_displacement hφ hφjets hn).trans
      (mul_le_mul (by dsimp only [B]; linarith [hP n])
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_left _ _) n) z))
        (add_nonneg zero_le_one (apply_nonneg _ _)) (hB n).le)
  rw [iteratedFDeriv_prodMk (hξ.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (hφ.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) le_rfl, ContinuousMultilinearMap.opNorm_prod]
  exact max_le (hradial' n) hangle

end ContinuousFlexibility.Analysis
