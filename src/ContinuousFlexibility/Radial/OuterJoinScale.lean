import ContinuousFlexibility.Radial.MorseAdjacentScaleBounds

/-!
# Adjacent scales in the transition-glue transfer estimate

The balanced transfer product on a glue contains one inverse departure
height and one arrival height.  Its scale is bounded by the smaller of
the two adjacent Morse coefficients, so the preceding glue can be
charged to the action of the transition cell itself.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- The numerical factor needed for glue transfer is uniformly bounded.
The minimum in the denominator retains the transition-cell action even
when the departure cell is the preceding, larger cell. -/
theorem morseAdjacentScale_transfer_factor_le
    (T : MorseChainData) (σ : ℕ → ℝ) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    {n m : ℕ} (hNn : T.index ≤ n) (hNm : T.index ≤ m)
    (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m) :
    (morseChainAmplitude T σ m / morseChainAmplitude T σ n) * morseChainA T m *
        (max (morseChainA T n) (morseChainA T m)) ^ 12 /
        (morseChainA T n ^ 5 * min (morseChainA T n) (morseChainA T m)) ≤ exp 400 := by
  let A := morseChainA T n
  let B := morseChainA T m
  let H := max A B
  let L := min A B
  let Q := morseChainAmplitude T σ m / morseChainAmplitude T σ n
  have hA : 0 < A := (by positivity : 0 < exp (-(n : ℝ) ^ 2) / 3).trans_le
    (morseChainA_exp_bounds T n hdn).1
  have hB : 0 < B := (by positivity : 0 < exp (-(m : ℝ) ^ 2) / 3).trans_le
    (morseChainA_exp_bounds T m hdm).1
  have hH : 0 < H := hA.trans_le (le_max_left A B)
  have hL : 0 < L := lt_min hA hB
  have hQ : 0 < Q := div_pos (morseChainAmplitude_pos T σ hσ m)
    (morseChainAmplitude_pos T σ hσ n)
  have hAn := abs_le.mp (morseChainA_log_error T n hdn)
  have hBm := abs_le.mp (morseChainA_log_error T m hdm)
  have hsq : (n : ℝ) ^ 2 - 2 * (n : ℝ) ≤ (m : ℝ) ^ 2 ∧
      (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 + 2 * (n : ℝ) + 1 := by
    rcases hadj with h | h
    · subst m
      push_cast
      constructor <;> nlinarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · subst n
      push_cast
      constructor <;> nlinarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hAlow : -(n : ℝ) ^ 2 - 8 ≤ log A := by linarith only [hAn.1]
  have hBlow : -(n : ℝ) ^ 2 - 2 * (n : ℝ) - 9 ≤ log B := by
    linarith only [hBm.1, hsq.2]
  have hAhigh : log A ≤ -(n : ℝ) ^ 2 + 2 * (n : ℝ) + 8 := by
    linarith only [hAn.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hBhigh : log B ≤ -(n : ℝ) ^ 2 + 2 * (n : ℝ) + 8 := by
    linarith only [hBm.2, hsq.1]
  have hHhigh : log H ≤ -(n : ℝ) ^ 2 + 2 * (n : ℝ) + 8 := by
    rcases le_total A B with hab | hba
    · rw [H, max_eq_right hab]
      exact hBhigh
    · rw [H, max_eq_left hba]
      exact hAhigh
  have hLlow : -(n : ℝ) ^ 2 - 2 * (n : ℝ) - 9 ≤ log L := by
    rcases le_total A B with hab | hba
    · rw [L, min_eq_left hab]
      linarith only [hAlow, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · rw [L, min_eq_right hba]
      exact hBlow
  have hQhigh := morseAdjacentScale_amplitude_log_bound T σ hσ hNn hNm hadj
  have hlogs : log Q + log B + 12 * log H - 5 * log A - log L ≤ 400 := by
    nlinarith only [hQhigh, hBhigh, hHhigh, hAlow, hLlow,
      sq_nonneg (12 * (n : ℝ) - 53)]
  change Q * B * H ^ 12 / (A ^ 5 * L) ≤ exp 400
  have hp : 0 < Q * B * H ^ 12 / (A ^ 5 * L) := by positivity
  apply (log_le_log_iff hp (exp_pos 400)).mp
  rw [log_exp, log_div (by positivity) (by positivity),
    log_mul (mul_ne_zero hQ.ne' hB.ne') (pow_ne_zero 12 hH.ne'),
    log_mul hQ.ne' hB.ne', log_mul (pow_ne_zero 5 hA.ne') hL.ne', log_pow, log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hlogs]

end ContinuousFlexibility.Radial
