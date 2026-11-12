import ContinuousFlexibility.Radial.InnerWeightRatios

/-!
# Fixed coefficient costs for neighboring physical labels

The true localizer and retained-piece indices differ by at most two.
One fixed coefficient power therefore absorbs their weight comparison
while preserving the exact signed attenuation exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

theorem matchedMorse_radialQ_succ_le {n : ℕ} (hn : 1 ≤ n) :
    radialQ (n + 1) ≤ 33 * radialQ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ log (exp 1 + (n : ℝ)) :=
    zero_le_one.trans (ssv_one_le_log (Nat.cast_nonneg n))
  have hp := mul_le_mul_of_nonneg_right
    (rpow_le_rpow_of_exponent_le hnR (by norm_num : (3 / 2 : ℝ) ≤ 5 / 2)) hlog
  have hterm : (n : ℝ) ^ (3 / 2 : ℝ) * log (exp 1 + n) ≤ radialQ n := hp
  have h := inner_weight_radialQ_succ_sub_le hn
  nlinarith only [h, hterm]

theorem matchedMorse_radialQ_near_le {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n + 2) :
    radialQ m ≤ 1089 * radialQ n := by
  have h₁ := matchedMorse_radialQ_succ_le hn
  have h₂ := matchedMorse_radialQ_succ_le (show 1 ≤ n + 1 by omega)
  have h₃ := radialQ_monotone hm
  have he : n + 1 + 1 = n + 2 := by omega
  rw [he] at h₂
  nlinarith only [h₁, h₂, h₃]

theorem matchedMorse_radialS_near_le {n m : ℕ} (hn : 2 ≤ n)
    (hl : n - 1 ≤ m) (hr : m ≤ n + 2) :
    |radialS m - radialS n| ≤ 32 * radialQ n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hnR) (by linarith only [hnR] : 0 ≤ 3 * (n : ℝ) + 1)
    nlinarith only [hh]
  have h₀ := inner_weight_radialS_succ_sub_le hn1
  have h₁ := inner_weight_radialS_succ_sub_le (show 1 ≤ n + 1 by omega)
  have hlow := inner_weight_radialS_succ_sub_le (show 1 ≤ n - 1 by omega)
  have he : n - 1 + 1 = n := by omega
  rw [he] at hlow
  simp only [Nat.cast_add, Nat.cast_one] at h₁
  have hprev : ((n - 1 : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
      (by exact_mod_cast Nat.sub_le n 1)
  have hQ := radial_nat_sq_le_Q n
  have hQ₀ := radialQ_nonneg n
  have hSmLo := radialS_monotone hl
  have hSmHi := radialS_monotone hr
  have he₂ : n + 1 + 1 = n + 2 := by omega
  rw [he₂] at h₁
  apply abs_le.mpr
  constructor <;> nlinarith only [h₀, h₁, hlow, hprev, hsq, hQ, hQ₀, hSmLo, hSmHi]

/-- The exact sign of S is retained; only the Q exponent changes. -/
theorem matchedMorse_piece_exp_near {n m : ℕ} {b σ : ℝ}
    (hn : 2 ≤ n) (hl : n - 1 ≤ m) (hr : m ≤ n + 2)
    (hb : 0 ≤ b) (hσ : |σ| ≤ 1) :
    exp (b * radialQ m + σ * radialS m) ≤
      exp ((1089 * b + 32) * radialQ n + σ * radialS n) := by
  have hQ := mul_le_mul_of_nonneg_left
    (matchedMorse_radialQ_near_le (show 1 ≤ n by omega) hr) hb
  have hS := matchedMorse_radialS_near_le hn hl hr
  have hσS : σ * (radialS m - radialS n) ≤ 32 * radialQ n := by
    calc
      _ ≤ |σ * (radialS m - radialS n)| := le_abs_self _
      _ = |σ| * |radialS m - radialS n| := abs_mul _ _
      _ ≤ |radialS m - radialS n| := mul_le_of_le_one_left (abs_nonneg _) hσ
      _ ≤ _ := hS
  exact exp_le_exp.mpr (by nlinarith only [hQ, hσS])

/-- A fixed interior seam index absorbs every initial localizer.
Its constant is selected before the retained transition or frequency. -/
theorem matchedMorse_piece_exp_initial {N J n m : ℕ} {a b σ : ℝ}
    (hn : n ≤ N) (hm : m ≤ J) (ha : 0 ≤ a) (hb : 0 ≤ b) (hσ : |σ| ≤ 1) :
    exp (b * radialQ m + σ * radialS m) ≤
      exp (b * radialQ J + radialS J + radialS N) *
        exp (a * radialQ n + σ * radialS n) := by
  have hSm : 0 ≤ radialS m := by unfold radialS; positivity
  have hSn : 0 ≤ radialS n := by unfold radialS; positivity
  have hs₁ := (abs_le.mp hσ).2
  have hs₂ : -σ ≤ 1 := by linarith only [(abs_le.mp hσ).1]
  have hms := mul_le_mul_of_nonneg_right hs₁ hSm
  have hns := mul_le_mul_of_nonneg_right hs₂ hSn
  have hQ := mul_le_mul_of_nonneg_left (radialQ_monotone hm) hb
  have hmS := radialS_monotone hm
  have hnS := radialS_monotone hn
  have haQ := mul_nonneg ha (radialQ_nonneg n)
  rw [← exp_add]
  apply exp_le_exp.mpr
  nlinarith only [hms, hns, hQ, hmS, hnS, haQ]

end ContinuousFlexibility.Radial
