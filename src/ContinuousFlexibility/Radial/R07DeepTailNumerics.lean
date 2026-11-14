module

public import ContinuousFlexibility.Radial.MorseJoinHeightContrast
public import ContinuousFlexibility.Radial.MorseRealizationBasic

/-!
# Numerical products on a fixed-frequency deep tail

The two indices incident to a resistance interval belong to `{n,n+1}`.
The same estimates therefore cover the original and shifted left indexing.
They are uniform over every admissible height sequence, and retain the
quadratic logarithmic gain required by the physical flatness statement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

theorem r07_amplitude_log_near (T : MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m g : ℕ}
    (hn : 1 ≤ n) (hN : T.index ≤ n)
    (hm : m = n ∨ m = n + 1) (hg : g = n ∨ g = n + 1) :
    |log (morseChainAmplitude T σ m / morseChainAmplitude T σ g)| ≤
      10 * (n : ℝ) ^ (3 / 2 : ℝ) + 1 := by
  have hp : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := rpow_nonneg (Nat.cast_nonneg n) _
  have hs := morseChainAmplitude_log_adjacent_bound T σ hσ hn hN
    (hN.trans (Nat.le_succ n)) (Or.inl rfl : n + 1 = n + 1 ∨ n = n + 1 + 1)
  rcases hm with hm | hm <;> rcases hg with hg | hg
  · rw [hm, hg, div_self (morseChainAmplitude_pos T σ hσ n).ne', log_one, abs_zero]
    positivity
  · have he : log (morseChainAmplitude T σ n / morseChainAmplitude T σ (n + 1)) =
        -log (morseChainAmplitude T σ (n + 1) / morseChainAmplitude T σ n) := by
      rw [log_div (morseChainAmplitude_pos T σ hσ n).ne'
          (morseChainAmplitude_pos T σ hσ (n + 1)).ne',
        log_div (morseChainAmplitude_pos T σ hσ (n + 1)).ne'
          (morseChainAmplitude_pos T σ hσ n).ne']
      ring
    rw [hm, hg, he, abs_neg]
    exact hs
  · simpa only [hm, hg] using hs
  · rw [hm, hg, div_self (morseChainAmplitude_pos T σ hσ (n + 1)).ne', log_one, abs_zero]
    positivity

theorem r07_A_log_near (T : MorseChainData) {n m : ℕ}
    (hd : T.d m = morseChainInteger m) (hm : m = n ∨ m = n + 1) :
    -((n : ℝ) + 1) ^ 2 - 8 ≤ log (morseChainA T m) ∧
      log (morseChainA T m) ≤ -(n : ℝ) ^ 2 + 8 := by
  have h := abs_le.mp (morseChainA_log_error T m hd)
  rcases hm with hm | hm
  · rw [hm] at h ⊢
    constructor <;> nlinarith only [h.1, h.2, Nat.cast_nonneg (α := ℝ) n]
  · rw [hm] at h ⊢
    push_cast at h
    constructor <;> nlinarith only [h.1, h.2, Nat.cast_nonneg (α := ℝ) n]

/-- Every adjacent mass/resistance product has the same leading logarithmic
gain; every adjacent gap/mass ratio has a strictly stronger loss. -/
theorem r07_deep_model_products (T : MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m g : ℕ}
    (hn : 1 ≤ n) (hN : T.index ≤ n)
    (hm : m = n ∨ m = n + 1) (hg : g = n ∨ g = n + 1)
    (hdm : T.d m = morseChainInteger m) (hdg : T.d g = morseChainInteger g) :
    exp (2 * (n : ℝ) ^ 2 - 10 * (n : ℝ) ^ (3 / 2 : ℝ) - 4 * n - 51) ≤
        (morseChainAmplitude T σ m / morseChainAmplitude T σ g) *
          morseChainA T m ^ 2 / morseChainA T g ^ 4 ∧
      (morseChainAmplitude T σ g / morseChainAmplitude T σ m) *
          morseChainA T g ^ 6 / morseChainA T m ^ 2 ≤
        exp (-4 * (n : ℝ) ^ 2 + 10 * (n : ℝ) ^ (3 / 2 : ℝ) + 4 * n + 67) := by
  have hAm : 0 < morseChainA T m :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T m hdm).1
  have hAg : 0 < morseChainA T g :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T g hdg).1
  have hlm := morseChainAmplitude_pos T σ hσ m
  have hlg := morseChainAmplitude_pos T σ hσ g
  have hamp := abs_le.mp (r07_amplitude_log_near T σ hσ hn hN hm hg)
  have hmA := r07_A_log_near T hdm hm
  have hgA := r07_A_log_near T hdg hg
  have hflip : log (morseChainAmplitude T σ g / morseChainAmplitude T σ m) =
      -log (morseChainAmplitude T σ m / morseChainAmplitude T σ g) := by
    rw [log_div hlg.ne' hlm.ne', log_div hlm.ne' hlg.ne']
    ring
  constructor
  · apply (le_log_iff_exp_le (by positivity)).mp
    rw [log_div (mul_ne_zero (div_ne_zero hlm.ne' hlg.ne') (pow_ne_zero 2 hAm.ne'))
        (pow_ne_zero 4 hAg.ne'),
      log_mul (div_ne_zero hlm.ne' hlg.ne') (pow_ne_zero 2 hAm.ne'), log_pow, log_pow]
    push_cast
    nlinarith only [hamp.1, hmA.1, hgA.2]
  · apply (log_le_iff_le_exp (by positivity)).mp
    rw [log_div (mul_ne_zero (div_ne_zero hlg.ne' hlm.ne') (pow_ne_zero 6 hAg.ne'))
        (pow_ne_zero 2 hAm.ne'),
      log_mul (div_ne_zero hlg.ne' hlm.ne') (pow_ne_zero 6 hAg.ne'), log_pow, log_pow,
      hflip]
    push_cast
    nlinarith only [hamp.1, hgA.2, hmA.1]

theorem r07_three_halves_young {x : ℝ} (hx : 0 ≤ x) :
    10 * x ^ (3 / 2 : ℝ) ≤ x ^ 2 + 25 * x := by
  by_cases hx0 : x = 0
  · subst x
    norm_num
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hp : x ^ (3 / 2 : ℝ) = x * sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      rpow_add hxp, rpow_one, ← sqrt_eq_rpow]
  rw [hp]
  nlinarith only [sq_nonneg (x - 5 * sqrt x), sq_sqrt hx]

theorem r07_deep_model_products_coarse (T : MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m g : ℕ}
    (hn : 32 ≤ n) (hN : T.index ≤ n)
    (hm : m = n ∨ m = n + 1) (hg : g = n ∨ g = n + 1)
    (hdm : T.d m = morseChainInteger m) (hdg : T.d g = morseChainInteger g) :
    exp (n : ℝ) ≤
        (morseChainAmplitude T σ m / morseChainAmplitude T σ g) *
          morseChainA T m ^ 2 / morseChainA T g ^ 4 ∧
      (morseChainAmplitude T σ g / morseChainAmplitude T σ m) *
          morseChainA T g ^ 6 / morseChainA T m ^ 2 ≤ exp (-(n : ℝ)) := by
  have hn' : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hx := r07_three_halves_young (Nat.cast_nonneg n)
  have hquad : 32 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hn') (Nat.cast_nonneg (α := ℝ) n)]
  have h := r07_deep_model_products T σ hσ (by omega) hN hm hg hdm hdg
  exact ⟨(exp_le_exp.mpr (by nlinarith only [hn', hx, hquad])).trans h.1,
    h.2.trans (exp_le_exp.mpr (by nlinarith only [hn', hx, hquad]))⟩

theorem r07_log_A_div_B_bound (T : MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) :
    0 ≤ log (morseChainA T n / morseChainB T n) ∧
      log (morseChainA T n / morseChainB T n) ≤ 8 * (n : ℝ) ^ 2 + 26 := by
  have hd2 : (2 : ℝ) ≤ T.d n := by
    rw [hd]
    exact_mod_cast morseChainInteger_ge_two n
  have hdp : 0 < (T.d n : ℝ) := (by norm_num : (0 : ℝ) < 2).trans_le hd2
  have hAB := morseChainParameters_pos T n hd2
  have hA : 0 < morseChainA T n := (mul_pos (by norm_num) hAB.2).trans hAB.1
  have hlogA := (abs_le.mp (morseChainA_log_error T n hd)).2
  have hdU : (T.d n : ℝ) ≤ 3 * exp ((n : ℝ) ^ 2) := by
    rw [hd]
    exact (morseChainInteger_lt n).le.trans
      (by linarith only [one_le_exp_iff.mpr (sq_nonneg (n : ℝ))])
  have hlogd := log_le_log hdp hdU
  rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (exp_ne_zero _), log_exp] at hlogd
  have hlog3 : log (3 : ℝ) ≤ 2 := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  constructor
  · apply log_nonneg
    apply (one_le_div hAB.2).mpr
    linarith only [hAB.1, hAB.2]
  · rw [log_div hA.ne' hAB.2.ne', morseChainB, log_rpow hdp]
    nlinarith only [hlogA, hlogd, hlog3]

/-- A polynomial bound is absorbed into one half of the Gaussian. This
leaves a plain exponential majorant convenient for a fixed frequency. -/
theorem r07_deep_small_scales (T : MorseChainData) {n : ℕ} (hn : 8 ≤ n)
    (hd : T.d n = morseChainInteger n) :
    morseChainA T n ^ 2 ≤ 81 * exp (-(n : ℝ)) ∧
      morseChainA T n ^ 2 * log (morseChainA T n / morseChainB T n) ≤
        81 * exp (-(n : ℝ)) := by
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : 64 ≤ (n : ℝ) ^ 2 := by nlinarith only [hn', sq_nonneg ((n : ℝ) - 8)]
  have hlin : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg hn0 (show 0 ≤ (n : ℝ) - 1 by linarith only [hn'])]
  have hAl := morseChainA_exp_bounds T n hd
  have hA : 0 ≤ morseChainA T n := sq_nonneg _
  have hA2 : morseChainA T n ^ 2 ≤ 81 * exp (-2 * (n : ℝ) ^ 2) := by
    have he : exp (-(n : ℝ) ^ 2) ^ 2 = exp (-2 * (n : ℝ) ^ 2) := by
      rw [← exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ (9 * exp (-(n : ℝ) ^ 2)) ^ 2 := pow_le_pow_left₀ hA hAl.2 2
      _ = _ := by rw [mul_pow, he]; norm_num
  have hpoly : 8 * (n : ℝ) ^ 2 + 26 ≤ exp ((n : ℝ) ^ 2) := by
    have he := add_one_le_exp ((n : ℝ) ^ 2 / 2)
    have he2 := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) ^ 2 / 2 + 1) he 2
    rw [← exp_nat_mul] at he2
    simp only [Nat.cast_ofNat] at he2
    have hexp : (2 : ℝ) * ((n : ℝ) ^ 2 / 2) = (n : ℝ) ^ 2 := by ring
    rw [hexp] at he2
    nlinarith only [he2, hsq,
      mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (n : ℝ))]
  constructor
  · exact hA2.trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by nlinarith only [hlin, sq_nonneg (n : ℝ)])) (by norm_num))
  · have hlog := r07_log_A_div_B_bound T n hd
    calc
      _ ≤ (81 * exp (-2 * (n : ℝ) ^ 2)) * exp ((n : ℝ) ^ 2) :=
        mul_le_mul hA2 (hlog.2.trans hpoly) hlog.1 (by positivity)
      _ = 81 * exp (-(n : ℝ) ^ 2) := by
        rw [mul_assoc, ← exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hlin)) (by norm_num)

end ContinuousFlexibility.Radial
