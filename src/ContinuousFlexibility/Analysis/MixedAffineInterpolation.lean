import ContinuousFlexibility.Analysis.SourceMixedOrderInterpolation

/-!
# A fixed budget for products of diagonal mixed-jet bounds

Two complementary spatial orders contribute only one common high
grading. The low order and the derivative loss are chosen before the
low-ball radius and the spatial order. This is the scalar estimate used
in the three-index Leibniz formula at fixed parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

theorem hasInterpolation_affine_mixed_product
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (lossA lossB requestedBase : ℕ) :
    ∃ B L : ℕ, requestedBase ≤ B ∧
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, a + b ≤ s → ∀ x w : E,
        p B x ≤ R → p B w ≤ 1 →
        (1 + p (a + lossA) x + p (a + lossA) w) *
          (1 + p (b + lossB) x + p (b + lossB) w) ≤
            C * (1 + p (s + L) x + p (s + L) w) := by
  obtain ⟨B, ℓ, hB, hb⟩ := hasInterpolation_oneHigh_height_local_growth
    p p hp hp hI hI 0 lossA lossB requestedBase
  let L : ℕ := B + max ℓ (max lossA lossB)
  have hℓ : ℓ ≤ max ℓ (max lossA lossB) := le_max_left _ _
  have hLA : lossA ≤ max ℓ (max lossA lossB) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hLB : lossB ≤ max ℓ (max lossA lossB) :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, L, (le_max_left _ _).trans hB, ?_⟩
  intro R hR s
  let κ : ℝ := max R 1
  have hκ : 0 ≤ κ := zero_le_one.trans (le_max_right _ _)
  obtain ⟨C₀, hC₀, hprod⟩ := hb 0 κ κ hκ hκ (s + B) (by omega)
  refine ⟨5 + 12 * C₀, by positivity, fun a b hab x w hx hw => ?_⟩
  let H : ℝ := 1 + p (s + L) x + p (s + L) w
  have hHx : p (s + L) x ≤ H := by
    dsimp only [H]
    linarith [apply_nonneg (p (s + L)) w]
  have hHw : p (s + L) w ≤ H := by
    dsimp only [H]
    linarith [apply_nonneg (p (s + L)) x]
  have hH1 : 1 ≤ H := by
    dsimp only [H]
    linarith [apply_nonneg (p (s + L)) x, apply_nonneg (p (s + L)) w]
  have hhigh : s + B + ℓ ≤ s + L := by dsimp only [L]; omega
  have hax : p (a + lossA) x ≤ H :=
    (hp (by dsimp only [L]; omega) x).trans hHx
  have haw : p (a + lossA) w ≤ H :=
    (hp (by dsimp only [L]; omega) w).trans hHw
  have hbx : p (b + lossB) x ≤ H :=
    (hp (by dsimp only [L]; omega) x).trans hHx
  have hbw : p (b + lossB) w ≤ H :=
    (hp (by dsimp only [L]; omega) w).trans hHw
  have hxκ : p B x ≤ κ := hx.trans (le_max_left _ _)
  have hwκ : p B w ≤ κ := hw.trans (le_max_right _ _)
  have hcross (y z : E) (hy : p B y ≤ κ) (hz : p B z ≤ κ)
      (hyH : p (s + L) y ≤ H) (hzH : p (s + L) z ≤ H) :
      p (a + lossA) y * p (b + lossB) z ≤ 3 * C₀ * H := by
    have h := hprod a (b + lossB) (by omega) y z (Fin.elim0 : Fin 0 → E × E)
      hy hz (fun i => Fin.elim0 i)
    have h' : (1 + p (a + lossA) y) * p (b + lossB) z ≤
        C₀ * (1 + p (s + B + ℓ) y + p (s + B + ℓ) z) := by
      simpa only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
        mul_one, add_zero, pairGrading_apply] using h
    have hy' := (hp hhigh y).trans hyH
    have hz' := (hp hhigh z).trans hzH
    calc
      _ ≤ (1 + p (a + lossA) y) * p (b + lossB) z :=
        mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)
      _ ≤ C₀ * (1 + p (s + B + ℓ) y + p (s + B + ℓ) z) := h'
      _ ≤ C₀ * (3 * H) := mul_le_mul_of_nonneg_left
        (by linarith only [hH1, hy', hz']) hC₀
      _ = _ := by ring
  have hxx := hcross x x hxκ hxκ hHx hHx
  have hxw := hcross x w hxκ hwκ hHx hHw
  have hwx := hcross w x hwκ hxκ hHw hHx
  have hww := hcross w w hwκ hwκ hHw hHw
  have hmain : (1 + p (a + lossA) x + p (a + lossA) w) *
      (1 + p (b + lossB) x + p (b + lossB) w) ≤ (5 + 12 * C₀) * H := by
    nlinarith only [hH1, hax, haw, hbx, hbw, hxx, hxw, hwx, hww]
  /- The coefficient below is written explicitly to keep the four
  complementary products visible in the estimate. -/
  exact hmain

end ContinuousFlexibility.Statements
