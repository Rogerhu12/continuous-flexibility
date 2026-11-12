import ContinuousFlexibility.Analysis.InteriorEndpointMaterialJets
import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds

/-!
# Fixed-loss jets of a genuinely transported circle label

The label and the angular endpoint map are estimated through their
displacements. Their values need no bound as circle lifts. Composition
uses the already proved one-high partition estimate, with one common
low order and loss before the input constants or the evaluation point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem positiveJet_material_of_linear_displacement
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {z : E}
    {f : X → ℝ} (hf : ContDiff ℝ ∞ f) (L : X →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {x : X} (hjets : PointwiseMaterialJetBound p loss A z (fun y => f y - L y) x)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (1 + A n) * (1 + p (n + loss) z) := by
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun y => f y - L y) x‖ + ‖L‖ :=
      norm_positiveJet_le_linear_displacement hf L hn x
    _ ≤ A n * (1 + p (n + loss) z) + 1 := add_le_add (hjets n) hL
    _ ≤ A n * (1 + p (n + loss) z) + (1 + p (n + loss) z) :=
      add_le_add le_rfl (le_add_of_nonneg_right (apply_nonneg _ _))
    _ = _ := by ring

theorem transportedLabel_displacement_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p low z ≤ 1 → ∀ u : ℝ → ℝ, ∀ g : PolarPoint → ℝ,
        ContDiff ℝ ∞ u → ContDiff ℝ ∞ g → ∀ x : PolarPoint,
        PointwiseMaterialJetBound p inputLoss A z (fun θ => u θ - θ) (g x) →
        PointwiseMaterialJetBound p inputLoss A z (fun y => g y - y.2) x →
        PointwiseMaterialJetBound p outLoss B z (fun y => u (g y) - y.2) x := by
  obtain ⟨low, outLoss, hcomposition⟩ :=
    coordinateComposition_fixed_loss_material_bound
      (X := PolarPoint) (Y := ℝ) (Z := ℝ) hp hI inputLoss
  refine ⟨low, max inputLoss outLoss, ?_⟩
  intro A hA
  let C : ℕ → ℝ := fun n => 1 + A n
  have hC (n : ℕ) : 1 ≤ C n := le_add_of_nonneg_right (hA n).le
  obtain ⟨Q, hQ, hbound⟩ := hcomposition C hC
  let B : ℕ → ℝ := fun n => if n = 0 then 2 * A 0 else Q (n - 1) + 1
  have hB (n : ℕ) : 0 < B n := by
    by_cases hn : n = 0
    · simpa only [B, if_pos hn] using mul_pos (by norm_num : (0 : ℝ) < 2) (hA 0)
    · simpa only [B, if_neg hn] using add_pos (hQ (n - 1)) zero_lt_one
  refine ⟨B, hB, ?_⟩
  intro z hz u g hu hg x hujets hgjets n
  by_cases hn : n = 0
  · subst n
    have huf : |u (g x) - g x| ≤ A 0 * (1 + p inputLoss z) := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.zero_add] using hujets 0
    have hgf : |g x - x.2| ≤ A 0 * (1 + p inputLoss z) := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.zero_add] using hgjets 0
    have hv : |u (g x) - x.2| ≤ 2 * A 0 * (1 + p inputLoss z) := by
      calc
        _ = |(u (g x) - g x) + (g x - x.2)| := congrArg abs (by ring)
        _ ≤ |u (g x) - g x| + |g x - x.2| := abs_add_le _ _
        _ ≤ A 0 * (1 + p inputLoss z) + A 0 * (1 + p inputLoss z) := add_le_add huf hgf
        _ = _ := by ring
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, B, if_pos rfl, Nat.zero_add]
    exact hv.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hp (le_max_left _ _) z))
      (mul_nonneg (by norm_num) (hA 0).le))
  · have hnpos : 1 ≤ n := by omega
    have huPositive (j : ℕ) (hj : 1 ≤ j) :
        ‖iteratedFDeriv ℝ j u (g x)‖ ≤
          C j * (1 : ℝ) ^ C j * (1 + p (j + inputLoss) z) := by
      simpa only [C, Real.one_rpow, mul_one] using
        positiveJet_material_of_linear_displacement hu (ContinuousLinearMap.id ℝ ℝ)
          (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)) hujets hj
    have hgPositive (j : ℕ) (hj : 1 ≤ j) :
        ‖iteratedFDeriv ℝ j g x‖ ≤
          C j * (1 : ℝ) ^ C j * (1 + p (j + inputLoss) z) := by
      simpa only [C, Real.one_rpow, mul_one] using
        positiveJet_material_of_linear_displacement hg (ContinuousLinearMap.snd ℝ ℝ ℝ)
          (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) hgjets hj
    have hc : ‖iteratedFDeriv ℝ n (u ∘ g) x‖ ≤
        Q (n - 1) * (1 + p (n + outLoss) z) := by
      have hcomp := hbound z hz 1 le_rfl u g x hu.contDiffAt hg.contDiffAt
        huPositive hgPositive (n - 1)
      have horder : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
      rw [horder] at hcomp
      simpa only [Real.one_rpow, mul_one] using hcomp
    have hsnd : ‖iteratedFDeriv ℝ n (fun y : PolarPoint => y.2) x‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.coe_snd'] using
        (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.snd ℝ ℝ ℝ) hnpos x).trans
          (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
    have hd : iteratedFDeriv ℝ n (fun y : PolarPoint => u (g y) - y.2) x =
        iteratedFDeriv ℝ n (u ∘ g) x - iteratedFDeriv ℝ n (fun y : PolarPoint => y.2) x :=
      iteratedFDeriv_sub_apply
        ((hu.comp hg).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) contDiffAt_snd
    have hb : ‖iteratedFDeriv ℝ n (fun y : PolarPoint => u (g y) - y.2) x‖ ≤
        (Q (n - 1) + 1) * (1 + p (n + outLoss) z) := by
      rw [hd]
      calc
        _ ≤ ‖iteratedFDeriv ℝ n (u ∘ g) x‖ +
            ‖iteratedFDeriv ℝ n (fun y : PolarPoint => y.2) x‖ := norm_sub_le _ _
        _ ≤ Q (n - 1) * (1 + p (n + outLoss) z) + 1 := add_le_add hc hsnd
        _ ≤ Q (n - 1) * (1 + p (n + outLoss) z) + (1 + p (n + outLoss) z) :=
          add_le_add le_rfl (le_add_of_nonneg_right (apply_nonneg _ _))
        _ = _ := by ring
    simp only [B, if_neg hn]
    exact hb.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_right inputLoss outLoss) n) z))
      (add_nonneg (hQ (n - 1)).le zero_le_one))

end ContinuousFlexibility.Analysis
