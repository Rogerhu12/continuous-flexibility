import ContinuousFlexibility.Radial.MorseChainParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Height contrast at adjacent Morse cells

The height on the right of a join uses the next cell's left speed, of size
`A`, and the height on the left uses the departing cell's right speed, of
size `A^5`. The exact adjacent amplitude recursion controls the remaining
logarithmic term in either direction along the chain.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set

set_option backward.isDefEq.respectTransparency false

theorem morseJoin_rpow_increment {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x + 1) ^ (5 / 2 : ℝ) - x ^ (5 / 2 : ℝ) ∧
      (x + 1) ^ (5 / 2 : ℝ) - x ^ (5 / 2 : ℝ) ≤
        (5 / 2 : ℝ) * (x + 1) ^ (3 / 2 : ℝ) := by
  let f : ℝ → ℝ := fun t => t ^ (5 / 2 : ℝ)
  have hf : Differentiable ℝ f := Real.differentiable_rpow_const (by norm_num)
  obtain ⟨t, ht, hDt⟩ := exists_deriv_eq_slope f (show x < x + 1 by linarith)
    hf.continuous.continuousOn hf.differentiableOn
  have hderiv : deriv f t = (5 / 2 : ℝ) * t ^ (3 / 2 : ℝ) := by
    change deriv (fun u : ℝ => u ^ (5 / 2 : ℝ)) t = _
    rw [Real.deriv_rpow_const, show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num]
  rw [hderiv, show x + 1 - x = 1 by ring, div_one] at hDt
  have hinc : (x + 1) ^ (5 / 2 : ℝ) - x ^ (5 / 2 : ℝ) =
      (5 / 2 : ℝ) * t ^ (3 / 2 : ℝ) := hDt.symm
  have ht₀ : 0 ≤ t := hx.trans ht.1.le
  rw [hinc]
  exact ⟨mul_nonneg (by norm_num) (Real.rpow_nonneg ht₀ _),
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht₀ ht.2.le (by norm_num)) (by norm_num)⟩

private theorem morseJoin_rpow_increment_nat (n : ℕ) :
    0 ≤ ((n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ) ∧
      ((n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ) ≤
        (5 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
  simpa only [Nat.cast_add, Nat.cast_one] using morseJoin_rpow_increment (Nat.cast_nonneg n)

private theorem morseJoin_rpow_increment_le (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ) ≤
      10 * (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := calc
    _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = _ := by norm_num [Real.rpow_two]
  have hmul : ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ 4 * (n : ℝ) ^ (3 / 2 : ℝ) := calc
    _ ≤ (2 * (n : ℝ)) ^ (3 / 2 : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      exact Real.rpow_le_rpow (by positivity) (by linarith only [hn₁]) (by norm_num)
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  calc
    _ ≤ (5 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
      (morseJoin_rpow_increment_nat n).2
    _ ≤ (5 / 2 : ℝ) * (4 * (n : ℝ) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ = _ := by ring

theorem morseChainAmplitude_log_succ (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) (n : ℕ) (hn : T.index ≤ n + 1) :
    log (Statements.morseChainAmplitude T σ (n + 1) / Statements.morseChainAmplitude T σ n) =
      log (σ (n + 1)) - (((n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) - (n : ℝ) ^ (5 / 2 : ℝ)) := by
  have hcur := morseChainAmplitude_pos T σ hσ n
  have hnext := morseChainAmplitude_pos T σ hσ (n + 1)
  have hσp := zero_lt_one.trans_le (hσ (n + 1)).1
  rw [log_div hnext.ne' hcur.ne', morseChainAmplitude_succ T σ n hn,
    log_mul (mul_ne_zero hσp.ne' (exp_ne_zero _)) hcur.ne',
    log_mul hσp.ne' (exp_ne_zero _), log_exp]
  ring

private theorem morseJoin_log_two_le : log (2 : ℝ) ≤ 1 := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
    log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)

private theorem morseJoin_log_sigma_bounds (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) (k : ℕ) : 0 ≤ log (σ k) ∧ log (σ k) ≤ 1 :=
  ⟨log_nonneg (hσ k).1,
    (log_le_log (zero_lt_one.trans_le (hσ k).1) (hσ k).2).trans morseJoin_log_two_le⟩

theorem morseChainAmplitude_log_adjacent_bound (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ} (hn : 1 ≤ n)
    (hNn : T.index ≤ n) (hNm : T.index ≤ m) (hadj : m = n + 1 ∨ n = m + 1) :
    |log (Statements.morseChainAmplitude T σ m / Statements.morseChainAmplitude T σ n)| ≤
      10 * (n : ℝ) ^ (3 / 2 : ℝ) + 1 := by
  rcases hadj with h | h
  · subst m
    rw [morseChainAmplitude_log_succ T σ hσ n hNm]
    have hD₀ := (morseJoin_rpow_increment_nat n).1
    have hD := morseJoin_rpow_increment_le n hn
    have hlog := morseJoin_log_sigma_bounds σ hσ (n + 1)
    have hn₀ := Real.rpow_nonneg (Nat.cast_nonneg n) (3 / 2 : ℝ)
    exact abs_le.mpr ⟨by linarith only [hD, hlog.1],
      by linarith only [hD₀, hlog.2, hn₀]⟩
  · subst n
    have hcur := morseChainAmplitude_pos T σ hσ m
    have hnext := morseChainAmplitude_pos T σ hσ (m + 1)
    have hflip : log (Statements.morseChainAmplitude T σ m /
        Statements.morseChainAmplitude T σ (m + 1)) =
        -log (Statements.morseChainAmplitude T σ (m + 1) / Statements.morseChainAmplitude T σ m) := by
      rw [log_div hcur.ne' hnext.ne', log_div hnext.ne' hcur.ne']
      ring
    rw [hflip, abs_neg, morseChainAmplitude_log_succ T σ hσ m hNn]
    have hD := morseJoin_rpow_increment_nat m
    have hlog := morseJoin_log_sigma_bounds σ hσ (m + 1)
    have hn₀ := Real.rpow_nonneg (Nat.cast_nonneg (m + 1)) (3 / 2 : ℝ)
    exact abs_le.mpr ⟨by linarith only [hD.2, hlog.1, hn₀],
      by linarith only [hD.1, hlog.2, hn₀]⟩

theorem morseChainA_log_error (T : Statements.MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) :
    |log (Statements.morseChainA T n) + (n : ℝ) ^ 2| ≤ 8 := by
  have hA := morseChainA_exp_bounds T n hd
  have hp : 0 < exp (-(n : ℝ) ^ 2) / 3 := div_pos (exp_pos _) (by norm_num)
  have hAl := log_le_log hp hA.1
  have hAh := log_le_log (hp.trans_le hA.1) hA.2
  rw [log_div (exp_ne_zero _) (by norm_num : (3 : ℝ) ≠ 0), log_exp] at hAl
  rw [log_mul (by norm_num : (9 : ℝ) ≠ 0) (exp_ne_zero _), log_exp] at hAh
  have h3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  have h9 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
  exact abs_le.mpr ⟨by linarith only [hAl, h3], by linarith only [hAh, h9]⟩

private theorem morseJoin_log_of_half_le_le_two {x : ℝ} (hx : 1 / 2 ≤ x ∧ x ≤ 2) :
    -1 ≤ log x ∧ log x ≤ 1 := by
  have hlo := log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hx.1
  rw [one_div, log_inv] at hlo
  exact ⟨by linarith only [hlo, morseJoin_log_two_le],
    (log_le_log ((by norm_num : (0 : ℝ) < 1 / 2).trans_le hx.1) hx.2).trans
      morseJoin_log_two_le⟩

/-- The placement relation bounds the ratio of the two actual radius dilations. -/
theorem morseJoin_scaleRatio_log_bound {Sn Sm rn rm ε : ℝ}
    (hSn : 0 < Sn) (hSm : 0 < Sm) (hrn : 1 / 2 ≤ rn ∧ rn ≤ 2)
    (hrm : 1 / 2 ≤ rm ∧ rm ≤ 2) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hmatch : Sm * rm = Sn * rn * (1 + ε)) : |log (Sm / Sn)| ≤ 3 := by
  have hrnp := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hrn.1
  have hrmp := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hrm.1
  have hεp : 0 < 1 + ε := by linarith only [hε.1]
  have he := congrArg Real.log hmatch
  rw [log_mul hSm.ne' hrmp.ne', log_mul (mul_ne_zero hSn.ne' hrnp.ne') hεp.ne',
    log_mul hSn.ne' hrnp.ne'] at he
  have hn := morseJoin_log_of_half_le_le_two hrn
  have hm := morseJoin_log_of_half_le_le_two hrm
  have hεl : 0 ≤ log (1 + ε) := log_nonneg (by linarith only [hε.1])
  have hεu : log (1 + ε) ≤ 1 :=
    (log_le_log hεp (by linarith only [hε.2])).trans morseJoin_log_two_le
  rw [log_div hSm.ne' hSn.ne']
  exact abs_le.mpr ⟨by linarith only [he, hn.1, hm.2, hεl],
    by linarith only [he, hn.2, hm.1, hεu]⟩

private theorem morseJoin_normalized_speed_log_bounds {p q : ℝ}
    (hp : 1 / 4 ≤ p ∧ p ≤ 7) (hq : 1 / 100 ≤ q ∧ q ≤ 3 / 100) :
    0 ≤ log (p / q) ∧ log (p / q) ≤ 10 := by
  have hq₀ := (by norm_num : (0 : ℝ) < 1 / 100).trans_le hq.1
  have hlo : 1 ≤ p / q := (le_div_iff₀ hq₀).mpr (by linarith only [hp.1, hq.2])
  have hhi : p / q ≤ (2 : ℝ) ^ 10 := calc
    _ ≤ 700 := (div_le_iff₀ hq₀).mpr (by linarith only [hp.2, hq.1])
    _ ≤ _ := by norm_num
  have hlog := log_le_log (zero_lt_one.trans_le hlo) hhi
  rw [log_pow] at hlog
  exact ⟨log_nonneg hlo, by linarith only [hlog, morseJoin_log_two_le]⟩

private theorem morseJoin_adjacent_square_bound {n m : ℕ} (hadj : m = n + 1 ∨ n = m + 1) :
    |(n : ℝ) ^ 2 - (m : ℝ) ^ 2| ≤ 2 * (n : ℝ) + 1 := by
  rcases hadj with h | h
  · subst m
    rw [Nat.cast_add, Nat.cast_one]
    apply abs_le.mpr
    constructor <;> nlinarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · subst n
    rw [Nat.cast_add, Nat.cast_one]
    apply abs_le.mpr
    constructor <;> nlinarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem morseJoin_height_log_range_of_error {n : ℕ} {x : ℝ} (hn : 100 ≤ n)
    (hx : |x - 4 * (n : ℝ) ^ 2| ≤ 10 * (n : ℝ) ^ (3 / 2 : ℝ) + 2 * (n : ℝ) + 63) :
    2 * (n : ℝ) ^ 2 ≤ x ∧ x ≤ 6 * (n : ℝ) ^ 2 := by
  have hn₁ : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := (by norm_num : (0 : ℝ) < 100).trans_le hn₁
  have hs : (10 : ℝ) ≤ sqrt n := calc
    _ = sqrt (100 : ℝ) := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)]
    _ ≤ _ := sqrt_le_sqrt hn₁
  have hp : (n : ℝ) ^ (3 / 2 : ℝ) * sqrt n = (n : ℝ) ^ 2 := by
    rw [sqrt_eq_rpow, ← Real.rpow_add hn₀,
      show (3 / 2 : ℝ) + 1 / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have ha : 10 * (n : ℝ) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ 2 := calc
    _ = (n : ℝ) ^ (3 / 2 : ℝ) * 10 := mul_comm _ _
    _ ≤ (n : ℝ) ^ (3 / 2 : ℝ) * sqrt n :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hn₀.le _)
    _ = _ := hp
  have hb : 2 * (n : ℝ) + 63 ≤ (n : ℝ) ^ 2 := calc
    _ ≤ 3 * (n : ℝ) := by linarith only [hn₁]
    _ ≤ _ := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right
        (show (3 : ℝ) ≤ n by linarith only [hn₁]) hn₀.le
  exact ⟨by linarith only [(abs_le.mp hx).1, ha, hb],
    by linarith only [(abs_le.mp hx).2, ha, hb]⟩

/-- A bound on the constant correction after accounting for the end cutoffs. -/
theorem morseJoin_height_budget {n : ℕ} {contrast drift span : ℝ} (hn : 100 ≤ n)
    (hcontrast : |contrast - 4 * (n : ℝ) ^ 2| ≤
      10 * (n : ℝ) ^ (3 / 2 : ℝ) + 2 * (n : ℝ) + 63)
    (hdrift : |drift| ≤ (n : ℝ) ^ 2) (hspan : 0 < span) :
    (n : ℝ) ^ 2 / span ≤ (contrast - drift) / span ∧
      (contrast - drift) / span ≤ 7 * (n : ℝ) ^ 2 / span := by
  have hrange := morseJoin_height_log_range_of_error hn hcontrast
  exact ⟨div_le_div_of_nonneg_right (by linarith only [hrange.1, (abs_le.mp hdrift).2]) hspan.le,
    div_le_div_of_nonneg_right (by linarith only [hrange.2, (abs_le.mp hdrift).1]) hspan.le⟩

/-- The actual adjacent height ratio in Section 5, in either radial orientation. -/
theorem morseJoin_height_log_contrast (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ} (hn : 1 ≤ n)
    (hNn : T.index ≤ n) (hNm : T.index ≤ m) (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m)
    {Sn Sm vn vm : ℝ} (hSn : 0 < Sn) (hSm : 0 < Sm) (hS : |log (Sm / Sn)| ≤ 3)
    (hvn : (1 / 100 : ℝ) * Statements.morseChainA T n ^ 5 ≤ vn ∧
      vn ≤ (3 / 100 : ℝ) * Statements.morseChainA T n ^ 5)
    (hvm : Statements.morseChainA T m / 4 ≤ vm ∧ vm ≤ 7 * Statements.morseChainA T m) :
    let WL := Statements.morseChainAmplitude T σ n * Sn * vn
    let WR := Statements.morseChainAmplitude T σ m * Sm * vm
    0 < WL ∧ 0 < WR ∧
      |log (WR / WL) - 4 * (n : ℝ) ^ 2| ≤ 10 * (n : ℝ) ^ (3 / 2 : ℝ) + 2 * (n : ℝ) + 63 ∧
      (100 ≤ n → 2 * (n : ℝ) ^ 2 ≤ log (WR / WL) ∧ log (WR / WL) ≤ 6 * (n : ℝ) ^ 2) := by
  let An := Statements.morseChainA T n
  let Am := Statements.morseChainA T m
  let ln := Statements.morseChainAmplitude T σ n
  let lm := Statements.morseChainAmplitude T σ m
  let WL := ln * Sn * vn
  let WR := lm * Sm * vm
  have hAn : 0 < An := (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
    (morseChainA_exp_bounds T n hdn).1
  have hAm : 0 < Am := (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
    (morseChainA_exp_bounds T m hdm).1
  have hln : 0 < ln := morseChainAmplitude_pos T σ hσ n
  have hlm : 0 < lm := morseChainAmplitude_pos T σ hσ m
  have hvnp : 0 < vn := (mul_pos (by norm_num) (pow_pos hAn 5)).trans_le hvn.1
  have hvmp : 0 < vm := (div_pos hAm (by norm_num)).trans_le hvm.1
  have hWL : 0 < WL := mul_pos (mul_pos hln hSn) hvnp
  have hWR : 0 < WR := mul_pos (mul_pos hlm hSm) hvmp
  let p := vm / Am
  let q := vn / An ^ 5
  have hp : 1 / 4 ≤ p ∧ p ≤ 7 := by
    refine ⟨(le_div_iff₀ hAm).mpr ?_, (div_le_iff₀ hAm).mpr hvm.2⟩
    calc
      _ = Am / 4 := by ring
      _ ≤ _ := hvm.1
  have hq : 1 / 100 ≤ q ∧ q ≤ 3 / 100 :=
    ⟨(le_div_iff₀ (pow_pos hAn 5)).mpr hvn.1, (div_le_iff₀ (pow_pos hAn 5)).mpr hvn.2⟩
  have hpp : 0 < p := div_pos hvmp hAm
  have hqp : 0 < q := div_pos hvnp (pow_pos hAn 5)
  have hlogWL : log WL = log ln + log Sn + log vn := by
    dsimp only [WL]
    rw [log_mul (mul_ne_zero hln.ne' hSn.ne') hvnp.ne', log_mul hln.ne' hSn.ne']
  have hlogWR : log WR = log lm + log Sm + log vm := by
    dsimp only [WR]
    rw [log_mul (mul_ne_zero hlm.ne' hSm.ne') hvmp.ne', log_mul hlm.ne' hSm.ne']
  have hlogp : log p = log vm - log Am := log_div hvmp.ne' hAm.ne'
  have hlogq : log q = log vn - 5 * log An := by
    dsimp only [q]
    rw [log_div hvnp.ne' (pow_ne_zero 5 hAn.ne'), log_pow]
    norm_num
  have he : log (WR / WL) =
      log (lm / ln) + log (Sm / Sn) + log (p / q) + log Am - 5 * log An := by
    rw [log_div hWR.ne' hWL.ne', hlogWR, hlogWL, log_div hlm.ne' hln.ne',
      log_div hSm.ne' hSn.ne', log_div hpp.ne' hqp.ne', hlogp, hlogq]
    ring
  have hAnlog : |log An + (n : ℝ) ^ 2| ≤ 8 := morseChainA_log_error T n hdn
  have hAmlog : |log Am + (m : ℝ) ^ 2| ≤ 8 := morseChainA_log_error T m hdm
  have hlam : |log (lm / ln)| ≤ 10 * (n : ℝ) ^ (3 / 2 : ℝ) + 1 :=
    morseChainAmplitude_log_adjacent_bound T σ hσ hn hNn hNm hadj
  have hsq := morseJoin_adjacent_square_bound hadj
  have hvlog := morseJoin_normalized_speed_log_bounds hp hq
  have hcontrast : |log (WR / WL) - 4 * (n : ℝ) ^ 2| ≤
      10 * (n : ℝ) ^ (3 / 2 : ℝ) + 2 * (n : ℝ) + 63 := by
    rw [he]
    have hnlog := abs_le.mp hAnlog
    have hmlog := abs_le.mp hAmlog
    have hlog := abs_le.mp hlam
    have hdiff := abs_le.mp hsq
    have hs := abs_le.mp hS
    exact abs_le.mpr ⟨by linarith only [hnlog.2, hmlog.1, hlog.1, hdiff.1, hs.1, hvlog.1],
      by linarith only [hnlog.1, hmlog.2, hlog.2, hdiff.2, hs.2, hvlog.2]⟩
  exact ⟨hWL, hWR, hcontrast, fun h100 => morseJoin_height_log_range_of_error h100 hcontrast⟩

end ContinuousFlexibility.Radial
