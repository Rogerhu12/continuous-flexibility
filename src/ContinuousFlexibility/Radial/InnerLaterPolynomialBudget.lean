import ContinuousFlexibility.Radial.HeightBandCount

/-!
# One numerical start absorbs every fixed later inverse coefficient

The start depends on the already chosen constants, before choosing a
selected tail.  Only the actual band upper endpoint and d_n identity
are used, so any larger actual starting index is permitted.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

theorem inner_later_frequency_bound {T : MorseChainData} {Cstar : ℝ}
    (hCstar : 0 ≤ Cstar) {n j : ℕ} (hd : T.d n = morseChainInteger n)
    (hband : radialFrequencyBand T Cstar n j) :
    (j : ℝ) ≤ 2 * Cstar * radialE n ^ 2 := by
  have hQ0 : 0 ≤ radialQ n := (sq_nonneg _).trans (radial_nat_sq_le_Q n)
  have hQ : radialQ n ≤ radialE n := by
    change radialQ n ≤ exp (radialQ n)
    linarith only [add_one_le_exp (radialQ n)]
  have hexp : exp ((n : ℝ) ^ 2 / 2) ≤ radialE n := by
    apply exp_le_exp.mpr
    nlinarith only [radial_nat_sq_le_Q n, sq_nonneg (n : ℝ)]
  calc
    (j : ℝ) ≤ 2 * Cstar * radialQ n * exp ((n : ℝ) ^ 2 / 2) :=
      hband.2.2.le.trans (radialFrequencyThreshold_le_exp T hCstar n hd)
    _ ≤ 2 * Cstar * radialE n * radialE n :=
      mul_le_mul (mul_le_mul_of_nonneg_left hQ (mul_nonneg (by norm_num) hCstar)) hexp
        (exp_pos _).le (mul_nonneg (mul_nonneg (by norm_num) hCstar) (exp_pos _).le)
    _ = _ := by ring

theorem exists_inner_later_budget_start {d p r Cstar : ℝ}
    (hCstar : 0 ≤ Cstar) (hp : 0 ≤ p) (hr : 0 ≤ r) (initial : ℕ) :
    ∃ N : ℕ, initial ≤ N ∧ ∀ (T : MorseChainData) (n j : ℕ), N ≤ n →
      T.d n = morseChainInteger n → radialFrequencyBand T Cstar n j →
      d * radialE n ^ (37 : ℝ) + p * (1 + (j : ℝ)) ^ 4 + r ≤
        radialE n ^ (38 : ℝ) := by
  let coeff : ℝ := |d| + p * (1 + 2 * Cstar) ^ 4 + r
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge coeff
  refine ⟨max initial (max 1 N₀), le_max_left _ _, ?_⟩
  intro T n j hn hd hband
  have hn1 : 1 ≤ n := (le_max_left 1 N₀).trans ((le_max_right _ _).trans hn)
  have hnN : N₀ ≤ n := (le_max_right 1 N₀).trans ((le_max_right _ _).trans hn)
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hE1 : 1 ≤ radialE n := by
    apply one_le_exp
    exact (sq_nonneg _).trans (radial_nat_sq_le_Q n)
  have hE0 : 0 ≤ radialE n := zero_le_one.trans hE1
  have hnE : (n : ℝ) ≤ radialE n := by
    have hnQ : (n : ℝ) ≤ radialQ n := by
      nlinarith only [hn1r, radial_nat_sq_le_Q n, sq_nonneg ((n : ℝ) - 1)]
    change (n : ℝ) ≤ exp (radialQ n)
    linarith only [hnQ, add_one_le_exp (radialQ n)]
  have hcoeff : coeff ≤ radialE n :=
    hN₀.trans ((Nat.cast_le.mpr hnN).trans hnE)
  have hj := inner_later_frequency_bound hCstar hd hband
  have hEsq : 1 ≤ radialE n ^ 2 := by nlinarith only [hE1]
  have hj' : 1 + (j : ℝ) ≤ (1 + 2 * Cstar) * radialE n ^ 2 := by
    nlinarith only [hj, hEsq]
  have hp4 : (1 + (j : ℝ)) ^ 4 ≤ (1 + 2 * Cstar) ^ 4 * radialE n ^ 8 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (j : ℝ)) hj' 4
    simpa only [mul_pow, ← pow_mul] using h
  have h8 : radialE n ^ 8 ≤ radialE n ^ 37 :=
    pow_le_pow_right₀ hE1 (by norm_num : 8 ≤ 37)
  have h37 : 1 ≤ radialE n ^ 37 := one_le_pow₀ hE1
  have hpoly : p * (1 + (j : ℝ)) ^ 4 ≤
      (p * (1 + 2 * Cstar) ^ 4) * radialE n ^ 37 := by
    calc
      _ ≤ p * ((1 + 2 * Cstar) ^ 4 * radialE n ^ 8) :=
        mul_le_mul_of_nonneg_left hp4 hp
      _ ≤ p * ((1 + 2 * Cstar) ^ 4 * radialE n ^ 37) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h8 (pow_nonneg (by linarith only [hCstar]) 4)) hp
      _ = _ := by ring
  have hr' : r ≤ r * radialE n ^ 37 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h37 hr
  have hd' : d * radialE n ^ 37 ≤ |d| * radialE n ^ 37 :=
    mul_le_mul_of_nonneg_right (le_abs_self d) (pow_nonneg hE0 37)
  simp only [rpow_natCast]
  calc
    _ ≤ |d| * radialE n ^ 37 +
        (p * (1 + 2 * Cstar) ^ 4) * radialE n ^ 37 + r * radialE n ^ 37 :=
      add_le_add (add_le_add hd' hpoly) hr'
    _ = coeff * radialE n ^ 37 := by dsimp only [coeff]; ring
    _ ≤ radialE n * radialE n ^ 37 :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hE0 37)
    _ = radialE n ^ 38 := by ring

end ContinuousFlexibility.Radial
