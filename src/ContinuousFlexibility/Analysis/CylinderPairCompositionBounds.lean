import ContinuousFlexibility.Analysis.CylinderMixedJetNorms
import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds

/-!
# A common fixed loss for actual scalar functions of two cylinder fields

The actual mixed jets of both inputs control their Fréchet jets. The
existing partition/interpolation estimate is applied once to the pair.
The low order and loss are independent of the outer function, its compact
range bounds, the cylinder domain, and the requested derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem cylinderPairComposition_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A D : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 →
      ∀ U : Set PolarPoint, IsOpen U →
      ∀ u v : PolarPoint → ℝ, ∀ Φ : PolarPoint → ℝ,
        ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U → ContDiff ℝ ∞ Φ →
        (∀ q ∈ U, ∀ k : ℕ, ‖iteratedFDeriv ℝ k Φ (u q, v q)‖ ≤ D k) →
        (∀ q ∈ U, ∀ a b : ℕ, |mixedDerivative a b u q| ≤
          A (a + b) * (1 + p (a + b + inputLoss) z)) →
        (∀ q ∈ U, ∀ a b : ℕ, |mixedDerivative a b v q| ≤
          A (a + b) * (1 + p (a + b + inputLoss) z)) →
        ∀ a b : ℕ, ∀ q ∈ U,
          |mixedDerivative a b (Φ ∘ fun y => (u y, v y)) q| ≤
            B (a + b) * (1 + p (a + b + loss) z) := by
  obtain ⟨base, loss, hclosure⟩ :=
    coordinateComposition_fixed_loss_material_bound
      (X := PolarPoint) (Y := PolarPoint) (Z := ℝ) hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A D hA
  let A' : ℕ → ℝ := fun k => 1 + |D k| + (2 : ℝ) ^ k * A k
  have hA' (k : ℕ) : 1 ≤ A' k := by
    have hAk : 0 ≤ A k := zero_le_one.trans (hA k)
    have hterm : 0 ≤ (2 : ℝ) ^ k * A k :=
      mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k) hAk
    dsimp only [A']
    linarith [abs_nonneg (D k)]
  obtain ⟨C, hC, hbound⟩ := hclosure A' hA'
  let B : ℕ → ℝ := fun n => 1 + |D 0| + C (n - 1)
  have hB (n : ℕ) : 0 < B n := by
    dsimp only [B]
    linarith [abs_nonneg (D 0), hC (n - 1)]
  refine ⟨B, hB, ?_⟩
  intro z hz U hU u v Φ hu hv hΦ houter hujet hvjet a b q hq
  let g : PolarPoint → PolarPoint := fun y => (u y, v y)
  have hg : ContDiffOn ℝ ∞ g U := hu.prodMk hv
  have hgq : ContDiffAt ℝ ∞ g q := hg.contDiffAt (hU.mem_nhds hq)
  have hcompose : ContDiffOn ℝ ∞ (Φ ∘ g) U := by
    intro y hy
    exact (hΦ.contDiffAt.comp y (hg.contDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  have hge (k : ℕ) : 1 ≤ 1 + p (k + inputLoss) z :=
    le_add_of_nonneg_right (apply_nonneg _ _)
  have hout (k : ℕ) (_ : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k Φ (g q)‖ ≤
        A' k * (1 : ℝ) ^ (A' k) * (1 + p (k + inputLoss) z) := by
    have hAk : 0 ≤ A k := zero_le_one.trans (hA k)
    have hDA : |D k| ≤ A' k := by
      dsimp only [A']
      nlinarith only [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k) hAk]
    have hval : ‖iteratedFDeriv ℝ k Φ (g q)‖ ≤ A' k :=
      (houter q hq k).trans ((le_abs_self _).trans hDA)
    simpa only [Real.one_rpow, mul_one] using hval.trans
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hge k) (zero_le_one.trans (hA' k)))
  have hin (k : ℕ) (_ : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k g q‖ ≤
        A' k * (1 : ℝ) ^ (A' k) * (1 + p (k + inputLoss) z) := by
    have hM : 0 ≤ A k * (1 + p (k + inputLoss) z) :=
      mul_nonneg (zero_le_one.trans (hA k)) (zero_le_one.trans (hge k))
    have hu' : ‖iteratedFDeriv ℝ k u q‖ ≤
        (2 : ℝ) ^ k * (A k * (1 + p (k + inputLoss) z)) := by
      apply norm_iteratedFDeriv_le_of_mixedDerivative hU hu k hq hM
      intro i j hij
      simpa only [Real.norm_eq_abs, hij] using hujet q hq i j
    have hv' : ‖iteratedFDeriv ℝ k v q‖ ≤
        (2 : ℝ) ^ k * (A k * (1 + p (k + inputLoss) z)) := by
      apply norm_iteratedFDeriv_le_of_mixedDerivative hU hv k hq hM
      intro i j hij
      simpa only [Real.norm_eq_abs, hij] using hvjet q hq i j
    have hpair : ‖iteratedFDeriv ℝ k g q‖ ≤
        (2 : ℝ) ^ k * (A k * (1 + p (k + inputLoss) z)) := by
      change ‖iteratedFDeriv ℝ k (fun y => (u y, v y)) q‖ ≤ _
      rw [iteratedFDeriv_prodMk
        ((hu.contDiffAt (hU.mem_nhds hq)).of_le (by simp : (k : ℕ∞ω) ≤ ∞))
        ((hv.contDiffAt (hU.mem_nhds hq)).of_le (by simp : (k : ℕ∞ω) ≤ ∞)) le_rfl,
        ContinuousMultilinearMap.opNorm_prod]
      exact max_le hu' hv'
    have hscale : (2 : ℝ) ^ k * A k ≤ A' k := by
      dsimp only [A']
      linarith [abs_nonneg (D k)]
    simpa only [Real.one_rpow, mul_one] using hpair.trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hscale (zero_le_one.trans (hge k)))
  have hhigh : 1 ≤ 1 + p (a + b + loss) z :=
    le_add_of_nonneg_right (apply_nonneg _ _)
  by_cases hzero : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    have hval : |Φ (g q)| ≤ D 0 := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using houter q hq 0
    have hDB : D 0 ≤ B 0 := by
      dsimp only [B]
      linarith [le_abs_self (D 0), hC (0 - 1)]
    have hfinal : |Φ (g q)| ≤ B 0 * (1 + p (0 + 0 + loss) z) :=
      (hval.trans hDB).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hhigh (hB 0).le)
    simpa only [mixedDerivative, iteratedDeriv_zero, Function.comp_apply, Nat.zero_add]
      using hfinal
  · have horder : a + b - 1 + 1 = a + b := by omega
    have hc := hbound z hz 1 le_rfl Φ g q hΦ.contDiffAt hgq hout hin (a + b - 1)
    have hc' : ‖iteratedFDeriv ℝ (a + b) (Φ ∘ g) q‖ ≤
        C (a + b - 1) * (1 + p (a + b + loss) z) := by
      simpa only [Real.one_rpow, mul_one, horder] using hc
    have hCB : C (a + b - 1) ≤ B (a + b) := by
      dsimp only [B]
      linarith [abs_nonneg (D 0)]
    exact (abs_mixedDerivative_le_norm_iteratedFDeriv hU hcompose a b hq).trans
      (hc'.trans (mul_le_mul_of_nonneg_right hCB (zero_le_one.trans hhigh)))

end ContinuousFlexibility.Analysis
