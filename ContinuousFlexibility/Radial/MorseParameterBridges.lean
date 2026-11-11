import ContinuousFlexibility.Radial.MorseArithmeticGap
import ContinuousFlexibility.Radial.MorseTravelIntegral

/-!
# The return and zero-gap bounds for the chosen Morse parameters

The actual travel integral and the integer norm estimates are specialized
to the same nonsquare integer parameter as in R04.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real

theorem morseParameter_return_and_level_gaps {d : ℕ} (hd : 1 < d)
    (hns : ¬ ∃ n : ℕ, n ^ 2 = d) :
    let A := ((d : ℝ) ^ (-1 / 2 : ℝ) + 2 * (d : ℝ) ^ (-9 / 2 : ℝ)) ^ 2
    let B := (d : ℝ) ^ (-9 : ℝ)
    4 * B < A ∧ 0 < B ∧
    Statements.morseTravel A B = π / (2 * sqrt d) ∧
    (∀ k : ℕ, 1 ≤ k → (3 * (k : ℝ) * sqrt d)⁻¹ ≤
      |sin ((k : ℝ) * Statements.morseTravel A B)|) ∧
    (∀ j : ℕ, 2 ≤ j → (8 * (d : ℝ) ^ 9)⁻¹ ≤ (j : ℝ) ^ 2 * B) ∧
    (∀ j : ℕ, 2 ≤ j → ∀ m : ℕ, (m : ℝ) < ((j : ℝ) * sqrt A - 1) / 2 →
      (8 * (d : ℝ) ^ 9)⁻¹ ≤ |Statements.morseLevel j A B m|) := by
  let x : ℝ := d
  let y := x ^ (-1 / 2 : ℝ)
  let t := x ^ (-9 / 2 : ℝ)
  let A := (y + 2 * t) ^ 2
  let B := x ^ (-9 : ℝ)
  change 4 * B < A ∧ 0 < B ∧ Statements.morseTravel A B = π / (2 * sqrt x) ∧ _
  have hx₁ : 1 ≤ x := by
    change (1 : ℝ) ≤ (d : ℝ)
    exact_mod_cast hd.le
  have hx : 0 < x := zero_lt_one.trans_le hx₁
  have hdn : 0 < d := zero_lt_one.trans hd
  have hB : 0 < B := rpow_pos_of_pos hx _
  have hy : 0 < y := rpow_pos_of_pos hx _
  have ht : 0 < t := rpow_pos_of_pos hx _
  have hsA : sqrt A = y + 2 * t := sqrt_sq (by positivity)
  have hsB : sqrt B = t := by
    dsimp only [B, t]
    rw [sqrt_eq_rpow, ← rpow_mul hx.le]
    congr 1
    norm_num
  have hBsq : B = t ^ 2 := by rw [← hsB, sq_sqrt hB.le]
  have hBpow : B = (x ^ (9 : ℕ))⁻¹ := by
    change x ^ (-(9 : ℝ)) = _
    rw [rpow_neg hx.le]
    exact congrArg (fun z : ℝ => z⁻¹) (rpow_natCast x 9)
  have hyinv : y = (sqrt x)⁻¹ := by
    change x ^ (-1 / 2 : ℝ) = _
    rw [sqrt_eq_rpow, ← rpow_neg hx.le]
    congr 1
    ring
  have hAB : 4 * B < A := by
    rw [hBsq]
    dsimp only [A]
    nlinarith only [mul_pos hy (show 0 < y + 4 * t by positivity)]
  have hgap : sqrt A - 2 * sqrt B = (sqrt x)⁻¹ := by
    rw [hsA, hsB, ← hyinv]
    ring
  have htravel : Statements.morseTravel A B = π / (2 * sqrt x) := by
    rw [morseTravel_eq_pi_sqrt hB hAB, hsA, hsB]
    have he : (y + 2 * t) / 2 - t = y / 2 := by ring
    rw [he, hyinv]
    simp only [div_eq_mul_inv, mul_inv_rev]
  have hpow : x ^ 5 ≤ x ^ 9 := by
    calc
      _ ≤ x ^ 5 * x ^ 4 :=
        le_mul_of_one_le_right (pow_nonneg hx.le _) (one_le_pow₀ hx₁)
      _ = _ := by rw [← pow_add]
  have hratio : sqrt B / sqrt x = (x ^ (5 : ℕ))⁻¹ := by
    rw [hsB, div_eq_mul_inv, ← hyinv]
    change x ^ (-9 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) = _
    rw [← rpow_add hx]
    rw [show (-9 / 2 : ℝ) + -1 / 2 = -5 by norm_num, rpow_neg hx.le]
    exact congrArg (fun z : ℝ => z⁻¹) (rpow_natCast x 5)
  have hlevel : (8 * x ^ 9)⁻¹ ≤ sqrt B / (6 * sqrt x) := by
    calc
      _ = 1 / (8 * x ^ 9) := by rw [one_div]
      _ ≤ 1 / (6 * x ^ 5) := one_div_le_one_div_of_le (by positivity)
        (by nlinarith only [hpow, pow_nonneg hx.le 5])
      _ = (sqrt B / sqrt x) / 6 := by
        rw [hratio]
        simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      _ = sqrt B / (6 * sqrt x) := by rw [div_div, mul_comm (sqrt x)]
  refine ⟨hAB, hB, htravel, ?_, ?_, ?_⟩
  · intro k hk
    rw [htravel]
    exact morse_return_small_divisor hdn hns hk
  · intro j hj
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
    change (8 * x ^ 9)⁻¹ ≤ (j : ℝ) ^ 2 * B
    rw [hBpow, mul_inv_rev, mul_comm ((x ^ 9)⁻¹)]
    exact mul_le_mul_of_nonneg_right (by
      calc
        (8 : ℝ)⁻¹ ≤ 4 := by norm_num
        _ ≤ (j : ℝ) ^ 2 := by nlinarith only [hj', sq_nonneg ((j : ℝ) - 2)])
      (inv_nonneg.mpr (pow_nonneg hx.le 9))
  · intro j hj m hm
    exact hlevel.trans (morse_discrete_level_gap hdn hns
      ((by decide : 1 ≤ 2).trans hj) hB hgap m hm)

end ContinuousFlexibility.Radial
