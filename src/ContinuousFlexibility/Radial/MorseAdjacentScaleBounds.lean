module

public import ContinuousFlexibility.Radial.MorseJoinHeightContrast

/-!
# Uniform numerical scales at adjacent Morse cells

The connector width in a realized chain is bounded by the twelfth power
of the coefficient at its connector index. Bounding that coefficient by
the maximum of the two incident coefficients treats both orientations
at once. The resulting mass and resistance factors are uniformly bounded
over every admissible height sequence and every retained index.

The proof includes index zero. A quadratic estimate for the adjacent
amplitude increment gives one numerical constant without any restriction
on the initial index of the chain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set

private theorem morseAdjacentScale_rpow_bound {x : ℝ} (hx : 0 ≤ x) :
    10 * x ^ (3 / 2 : ℝ) ≤ x ^ 2 + 25 * x := by
  by_cases hx0 : x = 0
  · subst x
    norm_num
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hp : x ^ (3 / 2 : ℝ) = x * sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hxp, Real.rpow_one, ← sqrt_eq_rpow]
  rw [hp]
  nlinarith only [sq_nonneg (x - 5 * sqrt x), sq_sqrt hx]

/-- The adjacent amplitude ratio has a quadratic logarithmic bound,
including the first possible departure index. -/
theorem morseAdjacentScale_amplitude_log_bound
    (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ}
    (hNn : T.index ≤ n) (hNm : T.index ≤ m)
    (hadj : m = n + 1 ∨ n = m + 1) :
    log (Statements.morseChainAmplitude T σ m / Statements.morseChainAmplitude T σ n) ≤
      (n : ℝ) ^ 2 + 25 * (n : ℝ) + 1 := by
  by_cases hn0 : n = 0
  · subst n
    have hm : m = 1 := by omega
    subst m
    have he := morseChainAmplitude_log_succ T σ hσ 0 hNm
    simp only [Nat.cast_zero, Nat.cast_one,
      Real.zero_rpow (by norm_num : (5 / 2 : ℝ) ≠ 0), Real.one_rpow] at he
    have hs : log (σ 1) ≤ 1 :=
      (log_le_log (zero_lt_one.trans_le (hσ 1).1) (hσ 1).2).trans
        (by simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
          log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2))
    rw [he]
    norm_num only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, zero_add]
    linarith only [hs]
  · have hn : 1 ≤ n := by omega
    have hlog := (abs_le.mp
      (morseChainAmplitude_log_adjacent_bound T σ hσ hn hNn hNm hadj)).2
    have hp := morseAdjacentScale_rpow_bound (Nat.cast_nonneg n)
    linarith only [hlog, hp]

private theorem morseAdjacentScale_coefficient_log_bounds
    (T : Statements.MorseChainData) {n m : ℕ}
    (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m) :
    -(n : ℝ) ^ 2 - 8 ≤ log (Statements.morseChainA T n) ∧
      log (Statements.morseChainA T m) ≤ -(n : ℝ) ^ 2 + 2 * (n : ℝ) + 8 ∧
      log (max (Statements.morseChainA T n) (Statements.morseChainA T m)) ≤
        -(n : ℝ) ^ 2 + 2 * (n : ℝ) + 8 := by
  have hn := abs_le.mp (morseChainA_log_error T n hdn)
  have hm := abs_le.mp (morseChainA_log_error T m hdm)
  have hsq : (n : ℝ) ^ 2 - 2 * (n : ℝ) ≤ (m : ℝ) ^ 2 := by
    rcases hadj with h | h
    · subst m
      push_cast
      nlinarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · subst n
      push_cast
      nlinarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hupperN : log (Statements.morseChainA T n) ≤
      -(n : ℝ) ^ 2 + 2 * (n : ℝ) + 8 := by
    linarith only [hn.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hupperM : log (Statements.morseChainA T m) ≤
      -(n : ℝ) ^ 2 + 2 * (n : ℝ) + 8 := by
    linarith only [hm.2, hsq]
  refine ⟨by linarith only [hn.1], hupperM, ?_⟩
  rcases le_total (Statements.morseChainA T n) (Statements.morseChainA T m) with h | h
  · rw [max_eq_right h]
    exact hupperM
  · rw [max_eq_left h]
    exact hupperN

/-- Logarithmic estimates for the exact numerical factors needed by
the connector integration bounds. No physical profile enters here. -/
theorem morseAdjacentScale_log_factors_bound
    (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ}
    (hNn : T.index ≤ n) (hNm : T.index ≤ m)
    (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m) :
    log (Statements.morseChainAmplitude T σ m / Statements.morseChainAmplitude T σ n) +
        log (Statements.morseChainA T m) +
        12 * log (max (Statements.morseChainA T n) (Statements.morseChainA T m)) -
        6 * log (Statements.morseChainA T n) ≤ 300 ∧
      12 * log (max (Statements.morseChainA T n) (Statements.morseChainA T m)) -
        log (Statements.morseChainA T n) ≤ 300 := by
  have hLam := morseAdjacentScale_amplitude_log_bound T σ hσ hNn hNm hadj
  obtain ⟨hlo, hhi, hmax⟩ := morseAdjacentScale_coefficient_log_bounds T hadj hdn hdm
  constructor
  · nlinarith only [hLam, hlo, hhi, hmax, sq_nonneg (12 * (n : ℝ) - 51)]
  · nlinarith only [hlo, hmax, sq_nonneg (11 * (n : ℝ) - 12)]

/-- Both adjacent scale factors have one universal bound. The maximum
coefficient covers the connector index in either radial orientation. -/
theorem morseAdjacentScale_factors_bound
    (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ}
    (hNn : T.index ≤ n) (hNm : T.index ≤ m)
    (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m) :
    (Statements.morseChainAmplitude T σ m / Statements.morseChainAmplitude T σ n) *
        Statements.morseChainA T m *
        (max (Statements.morseChainA T n) (Statements.morseChainA T m)) ^ 12 /
        Statements.morseChainA T n ^ 6 ≤ exp 300 ∧
      (max (Statements.morseChainA T n) (Statements.morseChainA T m)) ^ 12 /
        Statements.morseChainA T n ≤ exp 300 := by
  let A := Statements.morseChainA T n
  let B := Statements.morseChainA T m
  let H := max A B
  let Q := Statements.morseChainAmplitude T σ m / Statements.morseChainAmplitude T σ n
  have hA : 0 < A :=
    (by positivity : 0 < exp (-(n : ℝ) ^ 2) / 3).trans_le
      (morseChainA_exp_bounds T n hdn).1
  have hB : 0 < B :=
    (by positivity : 0 < exp (-(m : ℝ) ^ 2) / 3).trans_le
      (morseChainA_exp_bounds T m hdm).1
  have hH : 0 < H := hA.trans_le (le_max_left A B)
  have hQ : 0 < Q := div_pos (morseChainAmplitude_pos T σ hσ m)
    (morseChainAmplitude_pos T σ hσ n)
  have hLogs := morseAdjacentScale_log_factors_bound T σ hσ hNn hNm hadj hdn hdm
  change log Q + log B + 12 * log H - 6 * log A ≤ 300 ∧
    12 * log H - log A ≤ 300 at hLogs
  change Q * B * H ^ 12 / A ^ 6 ≤ exp 300 ∧ H ^ 12 / A ≤ exp 300
  constructor
  · have hp : 0 < Q * B * H ^ 12 / A ^ 6 := by positivity
    apply (log_le_log_iff hp (exp_pos 300)).mp
    rw [log_exp, log_div (by positivity) (pow_ne_zero 6 hA.ne'),
      log_mul (mul_ne_zero hQ.ne' hB.ne') (pow_ne_zero 12 hH.ne'),
      log_mul hQ.ne' hB.ne', log_pow, log_pow]
    simpa only [Nat.cast_ofNat] using hLogs.1
  · have hp : 0 < H ^ 12 / A := by positivity
    apply (log_le_log_iff hp (exp_pos 300)).mp
    rw [log_exp, log_div (pow_ne_zero 12 hH.ne') hA.ne', log_pow]
    simpa only [Nat.cast_ofNat] using hLogs.2

/-- A single constant works for all height choices and all adjacent
retained indices of any chain with the prescribed Morse integers. -/
theorem exists_morseAdjacentScaleBounds (T : Statements.MorseChainData)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ σ : ℕ → ℝ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      ∀ n m : ℕ, T.index ≤ n → T.index ≤ m → (m = n + 1 ∨ n = m + 1) →
        (Statements.morseChainAmplitude T σ m / Statements.morseChainAmplitude T σ n) *
            Statements.morseChainA T m *
            (max (Statements.morseChainA T n) (Statements.morseChainA T m)) ^ 12 /
            Statements.morseChainA T n ^ 6 ≤ K ∧
          (max (Statements.morseChainA T n) (Statements.morseChainA T m)) ^ 12 /
            Statements.morseChainA T n ≤ K := by
  refine ⟨exp 300, one_le_exp_iff.mpr (by norm_num), ?_⟩
  intro σ hσ n m hNn hNm hadj
  exact morseAdjacentScale_factors_bound T σ hσ hNn hNm hadj (hd n hNn) (hd m hNm)

end ContinuousFlexibility.Radial
