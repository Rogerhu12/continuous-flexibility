import ContinuousFlexibility.Analysis.PositivePowerMaterialJets
import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual radial power jets at a root

For a positive odd coefficient, the two actual functions
`((3/2) χ)^(2/3)` and `x ((3/2) χ)^(2/3)` inherit one common
fixed loss. Only the value of χ is restricted to a fixed positive
interval; its higher derivatives enter through the original field jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem rootRadialPower_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ l u : ℝ, 0 < l → l ≤ u →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ χ : ℝ × ℝ → ℝ, ∀ x : ℝ × ℝ,
      ContDiffAt ℝ ∞ χ x → x.1 = 0 → χ x ∈ Icc l u →
      PointwiseMaterialJetBound p inputLoss A z χ x →
      PointwiseMaterialJetBound p loss B z
          (fun y => ((3 / 2 : ℝ) * χ y) ^ (2 / 3 : ℝ)) x ∧
        PointwiseMaterialJetBound p loss B z
          (fun y => y.1 * ((3 / 2 : ℝ) * χ y) ^ (2 / 3 : ℝ)) x := by
  obtain ⟨powerBase, powerLoss, hpower⟩ :=
    positivePower_fixed_loss_material_bound (X := ℝ × ℝ) hp hI inputLoss
  obtain ⟨productBase, productLoss, hproduct⟩ :=
    pointwiseProduct_fixed_loss_material_bound (X := ℝ × ℝ) hp hI powerLoss
  refine ⟨max powerBase productBase, max powerLoss productLoss, ?_⟩
  intro A hA l u hl hlu
  let A' : ℕ → ℝ := fun n => |(3 / 2 : ℝ)| * A n
  have hA' (n : ℕ) : 0 < A' n :=
    mul_pos (by norm_num) (hA n)
  obtain ⟨D, hD, hfactor⟩ := hpower A' hA' ((3 / 2 : ℝ) * l)
    ((3 / 2 : ℝ) * u) (2 / 3 : ℝ) (mul_pos (by norm_num) hl)
    (mul_le_mul_of_nonneg_left hlu (by norm_num))
  let P : ℕ → ℝ := fun n => 1 + D n
  have hP (n : ℕ) : 0 < P n := add_pos zero_lt_one (hD n)
  obtain ⟨Q, hQ, hradial⟩ := hproduct P hP
  let B : ℕ → ℝ := fun n => D n + Q n
  have hB (n : ℕ) : 0 < B n := add_pos (hD n) (hQ n)
  refine ⟨B, hB, ?_⟩
  intro z hz χ x hχ hx hvalue hjet
  have hzPower : p powerBase z ≤ 1 :=
    ((hp (le_max_left _ _)) z).trans hz
  have hzProduct : p productBase z ≤ 1 :=
    ((hp (le_max_right _ _)) z).trans hz
  have hscaled : ContDiffAt ℝ ∞ (fun y => (3 / 2 : ℝ) * χ y) x :=
    contDiffAt_const.mul hχ
  have hscaledValue : (3 / 2 : ℝ) * χ x ∈
      Icc ((3 / 2 : ℝ) * l) ((3 / 2 : ℝ) * u) :=
    ⟨mul_le_mul_of_nonneg_left hvalue.1 (by norm_num),
      mul_le_mul_of_nonneg_left hvalue.2 (by norm_num)⟩
  have hscaledJet : PointwiseMaterialJetBound p inputLoss A' z
      (fun y => (3 / 2 : ℝ) * χ y) x :=
    hjet.const_mul hχ (3 / 2 : ℝ)
  have hfactorJet : PointwiseMaterialJetBound p powerLoss D z
      (fun y => ((3 / 2 : ℝ) * χ y) ^ (2 / 3 : ℝ)) x :=
    hfactor z hzPower _ x hscaled hscaledValue (fun n _ => hscaledJet n)
  have hfactorSmooth : ContDiffAt ℝ ∞
      (fun y => ((3 / 2 : ℝ) * χ y) ^ (2 / 3 : ℝ)) x :=
    hscaled.rpow_const_of_ne
      (mul_ne_zero (by norm_num) (ne_of_gt (hl.trans_le hvalue.1)))
  have hfirst : PointwiseMaterialJetBound p powerLoss (fun _ => (1 : ℝ)) z
      (fun y : ℝ × ℝ => y.1) x := by
    apply pointwiseMaterialJetBound_linear p powerLoss z
      (ContinuousLinearMap.fst ℝ ℝ ℝ) x zero_le_one
      (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
    change |x.1| ≤ 1
    rw [hx, abs_zero]
    exact zero_le_one
  have hfirstP : PointwiseMaterialJetBound p powerLoss P z
      (fun y : ℝ × ℝ => y.1) x :=
    hfirst.mono hp le_rfl (fun _ => zero_le_one)
      (fun n => le_add_of_nonneg_right (hD n).le)
  have hfactorP : PointwiseMaterialJetBound p powerLoss P z
      (fun y => ((3 / 2 : ℝ) * χ y) ^ (2 / 3 : ℝ)) x :=
    hfactorJet.mono hp le_rfl (fun n => (hD n).le)
      (fun _ => le_add_of_nonneg_left zero_le_one)
  have hradialJet : PointwiseMaterialJetBound p productLoss Q z
      (fun y => y.1 * ((3 / 2 : ℝ) * χ y) ^ (2 / 3 : ℝ)) x :=
    hradial z hzProduct _ _ x contDiffAt_fst hfactorSmooth hfirstP hfactorP
  exact ⟨hfactorJet.mono hp (le_max_left _ _) (fun n => (hD n).le)
      (fun n => le_add_of_nonneg_right (hQ n).le),
    hradialJet.mono hp (le_max_right _ _) (fun n => (hQ n).le)
      (fun n => le_add_of_nonneg_left (hD n).le)⟩

end ContinuousFlexibility.Analysis
