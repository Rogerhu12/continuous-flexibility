module

public import ContinuousFlexibility.Radial.MorseTransitionBands
public import ContinuousFlexibility.Radial.OuterCoreMassScale

/-!
# Quadratic exponential bounds within a transition frequency band

The frequency cutoff is polynomial times the inverse square root of the
actual Morse coefficient.  The resulting frequency powers and model
lengths have logarithms bounded by a constant times the square of the
cell index.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

def outerFrequencyExponent (C : ℝ) : ℝ := 9 + 3 * C ^ 2 * (exp 1 + 1) ^ 2

theorem outer_radialQ_exp_bound {n : ℕ} (hn : 1 ≤ n) :
    radialQ n ≤ (exp 1 + 1) * exp (4 * (n : ℝ)) := by
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnexp : (n : ℝ) ≤ exp (n : ℝ) :=
    (le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _)
  have hpow : (n : ℝ) ^ (5 / 2 : ℝ) ≤ exp (3 * (n : ℝ)) := by
    calc
      _ ≤ (n : ℝ) ^ (3 : ℝ) := rpow_le_rpow_of_exponent_le hn₁ (by norm_num)
      _ = (n : ℝ) ^ 3 := rpow_natCast _ 3
      _ ≤ exp (n : ℝ) ^ 3 := pow_le_pow_left₀ hn₀ hnexp 3
      _ = exp (3 * (n : ℝ)) := by
        calc
          _ = (exp (n : ℝ) * exp (n : ℝ)) * exp (n : ℝ) := by ring
          _ = exp (((n : ℝ) + n) + n) := by rw [exp_add, exp_add]
          _ = _ := by congr 1; ring
  have hlog : log (exp 1 + (n : ℝ)) ≤ (exp 1 + 1) * exp (n : ℝ) := by
    calc
      _ ≤ exp 1 + (n : ℝ) := log_le_self (by positivity)
      _ ≤ (exp 1 + 1) * ((n : ℝ) + 1) := by
        nlinarith only [hn₀, mul_nonneg (exp_pos (1 : ℝ)).le hn₀]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_one_le_exp _) (by positivity)
  have hlog₀ : 0 ≤ log (exp 1 + (n : ℝ)) :=
    log_nonneg (by linarith only [one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1), hn₀])
  unfold radialQ
  calc
    _ ≤ exp (3 * (n : ℝ)) * ((exp 1 + 1) * exp (n : ℝ)) :=
      mul_le_mul hpow hlog hlog₀ (exp_pos _).le
    _ = (exp 1 + 1) * exp (4 * (n : ℝ)) := by
      rw [mul_left_comm, ← exp_add]
      congr 2
      ring

theorem outer_frequency_sq_le_exp_of_upper {T : MorseChainData} {C : ℝ} {n j : ℕ}
    (hn : 1 ≤ n) (hd : T.d n = morseChainInteger n)
    (hupper : (j : ℝ) < radialFrequencyThreshold T C n) :
    (j : ℝ) ^ 2 ≤ exp (outerFrequencyExponent C * (n : ℝ) ^ 2) := by
  let A := morseChainA T n
  let F := 3 * C ^ 2 * (exp 1 + 1) ^ 2
  have hA : 0 < A := (by positivity : 0 < exp (-(n : ℝ) ^ 2) / 3).trans_le
    (morseChainA_exp_bounds T n hd).1
  have hband' : (j : ℝ) * sqrt A < C * radialQ n :=
    (lt_div_iff₀ (sqrt_pos.mpr hA)).mp hupper
  have hsq : (j : ℝ) ^ 2 * A ≤ C ^ 2 * radialQ n ^ 2 := by
    simpa only [mul_pow, sq_sqrt hA.le] using
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg j) (sqrt_nonneg A)) hband'.le 2
  have hQ₀ : 0 ≤ radialQ n := (sq_nonneg _).trans (radial_nat_sq_le_Q n)
  have hQ : radialQ n ^ 2 ≤ (exp 1 + 1) ^ 2 * exp (8 * (n : ℝ)) := by
    calc
      _ ≤ ((exp 1 + 1) * exp (4 * (n : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hQ₀ (outer_radialQ_exp_bound hn) 2
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [pow_two, ← exp_add]
        congr 1
        ring
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn', sq_nonneg ((n : ℝ) - 1)]
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hFexp := nonneg_le_exp_mul_nat_sq hF hn
  calc
    (j : ℝ) ^ 2 ≤ (C ^ 2 * radialQ n ^ 2) / A := (le_div_iff₀ hA).mpr hsq
    _ ≤ (C ^ 2 * ((exp 1 + 1) ^ 2 * exp (8 * (n : ℝ)))) / A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (sq_nonneg C)) hA.le
    _ ≤ (C ^ 2 * ((exp 1 + 1) ^ 2 * exp (8 * (n : ℝ)))) /
        (exp (-(n : ℝ) ^ 2) / 3) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (morseChainA_exp_bounds T n hd).1
    _ = F * exp ((n : ℝ) ^ 2 + 8 * (n : ℝ)) := by
      dsimp only [F]
      rw [exp_add, exp_neg]
      field_simp [exp_ne_zero ((n : ℝ) ^ 2)] <;> ring
    _ ≤ F * exp (9 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hn_sq])) hF
    _ ≤ exp (F * (n : ℝ) ^ 2) * exp (9 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hFexp (exp_pos _).le
    _ = exp (outerFrequencyExponent C * (n : ℝ) ^ 2) := by
      rw [← exp_add]
      congr 1
      dsimp only [F, outerFrequencyExponent]
      ring

theorem outer_frequency_sq_le_exp {T : MorseChainData} {C : ℝ} {n j : ℕ}
    (hn : 1 ≤ n) (hd : T.d n = morseChainInteger n)
    (hband : radialFrequencyBand T C n j) :
    (j : ℝ) ^ 2 ≤ exp (outerFrequencyExponent C * (n : ℝ) ^ 2) :=
  outer_frequency_sq_le_exp_of_upper hn hd hband.2.2

/-- The length of the negative model component is only quadratic in the
cell index. -/
theorem outer_morse_log_ratio_le {T : MorseChainData} {n : ℕ}
    (hn : 1 ≤ n) (hd : T.d n = morseChainInteger n) :
    log (morseChainA T n / morseChainB T n) ≤ 32 * (n : ℝ) ^ 2 := by
  let d : ℝ := T.d n
  let A := morseChainA T n
  let B := morseChainB T n
  have hd2 : 2 ≤ d := by
    change (2 : ℝ) ≤ (T.d n : ℝ)
    rw [hd]
    exact_mod_cast morseChainInteger_ge_two n
  have hd1 : 1 ≤ d := (by norm_num : (1 : ℝ) ≤ 2).trans hd2
  have hd0 : 0 < d := zero_lt_one.trans_le hd1
  have hB : 0 < B := (morseChainParameters_pos T n hd2).2
  have hA : 0 < A := (mul_pos (by norm_num : (0 : ℝ) < 4) hB).trans
    (morseChainParameters_pos T n hd2).1
  have hBp : B = (d ^ 9)⁻¹ := by
    change morseChainB T n = _
    rw [morseChainB_inv_pow T n hd0.le, inv_pow]
  have hratio : A / B ≤ 9 * d ^ 8 := by
    rw [hBp, div_inv_eq_mul]
    calc
      _ ≤ (9 * d⁻¹) * d ^ 9 := mul_le_mul_of_nonneg_right (morseChainA_inv_bounds T n hd1).2
        (pow_nonneg hd0.le _)
      _ = (9 * (d⁻¹ * d)) * d ^ 8 := by ring
      _ = _ := by rw [inv_mul_cancel₀ hd0.ne', mul_one]
  have hlog := log_le_log (div_pos hA hB) hratio
  rw [log_mul (by norm_num : (9 : ℝ) ≠ 0) (pow_ne_zero 8 hd0.ne'), log_pow] at hlog
  have hdU : d ≤ 3 * exp ((n : ℝ) ^ 2) := by
    calc
      _ = (morseChainInteger n : ℝ) := by dsimp only [d]; rw [hd]
      _ ≤ exp ((n : ℝ) ^ 2) + 2 := (morseChainInteger_lt n).le
      _ ≤ _ := by linarith only [one_le_exp_iff.mpr (sq_nonneg (n : ℝ))]
  have hdLog := log_le_log hd0 hdU
  rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (exp_ne_zero _), log_exp] at hdLog
  have hlog3 : log (3 : ℝ) ≤ 2 := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  have hlog9 : log (9 : ℝ) ≤ 8 := by
    simpa only [show (9 : ℝ) - 1 = 8 by norm_num] using log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith only [hlog, hdLog, hlog3, hlog9, hn', sq_nonneg ((n : ℝ) - 1)]

end ContinuousFlexibility.Radial
