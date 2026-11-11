import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# The coefficient envelope for the outer inverse

The actual quadratic core and natural-mass losses fit the manuscript's
E_n envelope uniformly for every n >= 1. These elementary comparisons
keep the action loss K_n separate from the coefficient envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

theorem outer_nat_sq_le_radialQ {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 ≤ radialQ n := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 1 ≤ sqrt (n : ℝ) := by
    simpa only [sqrt_one] using sqrt_le_sqrt hnR
  have hl := ssv_one_le_log (Nat.cast_nonneg n)
  rw [radialQ, ssv_rpow_five_half (Nat.cast_nonneg n)]
  calc
    (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * sqrt (n : ℝ) := by nlinarith [sq_nonneg (n : ℝ)]
    _ ≤ (n : ℝ) ^ 2 * sqrt (n : ℝ) * log (exp 1 + n) := by
      exact le_mul_of_one_le_right (by positivity) hl

theorem outer_radialE_rpow (n : ℕ) (C : ℝ) :
    radialE n ^ C = exp (C * radialQ n) := by
  rw [radialE, rpow_def_of_pos (exp_pos _), log_exp]
  congr 1
  ring

theorem outer_quadratic_le_envelope {n : ℕ} {C : ℝ} (hn : 1 ≤ n) (hC : 0 ≤ C) :
    exp (C * (n : ℝ) ^ 2) ≤ radialE n ^ C := by
  rw [outer_radialE_rpow]
  exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (outer_nat_sq_le_radialQ hn) hC)

/-- A whole-space block bound has precisely the requested E_n^C K_n^2
form once the actual mass, Poisson, and core state estimates are inserted. -/
theorem outer_inverse_envelope {n : ℕ} {C K d : ℝ}
    (hn : 1 ≤ n) (hC : 0 ≤ C) (hK : 1 ≤ K) (hd : d ≤ 4) :
    2 * (d + 2 * exp (C * (n : ℝ) ^ 2) ^ 2 * K ^ 2) ≤
      radialE n ^ (12 + 2 * C) * K ^ 2 := by
  have hA : 1 ≤ exp (C * (n : ℝ) ^ 2) :=
    one_le_exp_iff.mpr (mul_nonneg hC (sq_nonneg _))
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hA2 : 1 ≤ exp (C * (n : ℝ) ^ 2) ^ 2 := by nlinarith
  have hAK : 1 ≤ exp (C * (n : ℝ) ^ 2) ^ 2 * K ^ 2 :=
    one_le_mul_of_one_le_of_one_le hA2 hK2
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have he12 : 12 ≤ exp 12 := by linarith [add_one_le_exp (12 : ℝ)]
  have heq : exp (C * (n : ℝ) ^ 2) ^ 2 = exp (2 * C * (n : ℝ) ^ 2) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  calc
    _ ≤ 12 * exp (C * (n : ℝ) ^ 2) ^ 2 * K ^ 2 := by nlinarith
    _ ≤ exp 12 * exp (C * (n : ℝ) ^ 2) ^ 2 * K ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he12 (sq_nonneg _)) (sq_nonneg _)
    _ = exp (12 + 2 * C * (n : ℝ) ^ 2) * K ^ 2 := by rw [heq, exp_add]
    _ ≤ exp ((12 + 2 * C) * (n : ℝ) ^ 2) * K ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply exp_le_exp.mpr
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right (outer_quadratic_le_envelope hn (by positivity))
      (sq_nonneg _)

end ContinuousFlexibility.Radial
