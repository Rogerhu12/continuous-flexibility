import ContinuousFlexibility.Radial.CentralSmallDivisor
import ContinuousFlexibility.Radial.MorseChainParameters

/-!
# Arithmetic gaps for the Morse parameters

The same integer norm gives a distance from rational return phases and a
separation for each proposed discrete level. The spectral identification
and the evaluation of the actual optical integral are separate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real

private theorem morse_integer_norm_ne_zero {d k : ℕ}
    (hd : ¬ ∃ n : ℕ, n ^ 2 = d) (hk : 0 < k) (m : ℤ) :
    (k : ℤ) ^ 2 - (d : ℤ) * m ^ 2 ≠ 0 := by
  intro hn
  have hr : (k : ℝ) ^ 2 = (d : ℝ) * (m : ℝ) ^ 2 := by
    exact_mod_cast (sub_eq_zero.mp hn)
  by_cases hm : m = 0
  · subst m
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hr
    exact (sq_pos_of_pos hk').ne' hr
  · have hs : Irrational (sqrt (d : ℝ)) := irrational_sqrt_natCast_iff.mpr (by
      rintro ⟨n, hn'⟩
      exact hd ⟨n, by simpa only [pow_two] using hn'.symm⟩)
    have him : Irrational ((m : ℝ) * sqrt (d : ℝ)) := hs.intCast_mul hm
    have heq : (k : ℝ) ^ 2 = ((m : ℝ) * sqrt (d : ℝ)) ^ 2 := by
      rw [hr, mul_pow, sq_sqrt (Nat.cast_nonneg d), mul_comm]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
    · exact him.ne_nat k h.symm
    · exact him.neg.ne_nat k h.symm

theorem morse_integer_phase_gap {d k : ℕ}
    (hd : ¬ ∃ n : ℕ, n ^ 2 = d) (hk : 1 ≤ k) (m : ℤ) :
    1 / (3 * (k : ℝ)) ≤ |(k : ℝ) - (m : ℝ) * sqrt (d : ℝ)| := by
  let z : ℝ := (m : ℝ) * sqrt (d : ℝ)
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk₀ : (0 : ℝ) < k := zero_lt_one.trans_le hk₁
  have hpos : 0 < 3 * (k : ℝ) := by positivity
  change 1 / (3 * (k : ℝ)) ≤ |(k : ℝ) - z|
  by_cases hclose : |(k : ℝ) - z| ≤ 1
  · have hnorm : (1 : ℝ) ≤ |(k : ℝ) ^ 2 - (d : ℝ) * (m : ℝ) ^ 2| := by
      exact_mod_cast Int.one_le_abs (morse_integer_norm_ne_zero hd (Nat.succ_le_iff.mp hk) m)
    have hfactor : (k : ℝ) ^ 2 - (d : ℝ) * (m : ℝ) ^ 2 =
        ((k : ℝ) - z) * ((k : ℝ) + z) := by
      have hz : z ^ 2 = (d : ℝ) * (m : ℝ) ^ 2 := by
        dsimp [z]
        rw [mul_pow, sq_sqrt (Nat.cast_nonneg d), mul_comm]
      nlinarith only [hz]
    have hsum : |(k : ℝ) + z| ≤ 3 * (k : ℝ) := calc
      _ = |2 * (k : ℝ) - ((k : ℝ) - z)| := by congr 1; ring
      _ ≤ |2 * (k : ℝ)| + |(k : ℝ) - z| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg (by positivity)]; linarith only [hclose, hk₁]
    rw [hfactor, abs_mul] at hnorm
    exact (div_le_iff₀ hpos).mpr
      (hnorm.trans (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)))
  · apply le_trans _ (le_of_lt (lt_of_not_ge hclose))
    exact (div_le_iff₀ hpos).mpr (by linarith only [hk₁])

theorem morse_normalized_phase_gap {d k : ℕ} (hd₀ : 0 < d)
    (hd : ¬ ∃ n : ℕ, n ^ 2 = d) (hk : 1 ≤ k) (m : ℤ) :
    1 / (3 * (k : ℝ) * sqrt (d : ℝ)) ≤ |(k : ℝ) / sqrt (d : ℝ) - (m : ℝ)| := by
  have hs : 0 < sqrt (d : ℝ) := sqrt_pos.2 (by exact_mod_cast hd₀)
  calc
    _ = (1 / (3 * (k : ℝ))) / sqrt (d : ℝ) := by rw [div_div]
    _ ≤ |(k : ℝ) - (m : ℝ) * sqrt (d : ℝ)| / sqrt (d : ℝ) :=
      div_le_div_of_nonneg_right (morse_integer_phase_gap hd hk m) hs.le
    _ = |((k : ℝ) - (m : ℝ) * sqrt (d : ℝ)) / sqrt (d : ℝ)| := by
      rw [abs_div, abs_of_pos hs]
    _ = _ := by rw [sub_div, mul_div_cancel_right₀ _ hs.ne']

/-- The sine bound for the prescribed Morse return angle. -/
theorem morse_return_small_divisor {d k : ℕ} (hd₀ : 0 < d)
    (hd : ¬ ∃ n : ℕ, n ^ 2 = d) (hk : 1 ≤ k) :
    (3 * (k : ℝ) * sqrt (d : ℝ))⁻¹ ≤
      |sin ((k : ℝ) * (π / (2 * sqrt (d : ℝ))))| := by
  let y : ℝ := (k : ℝ) / (2 * sqrt (d : ℝ))
  let m := round y
  have hs : 0 < sqrt (d : ℝ) := sqrt_pos.2 (by exact_mod_cast hd₀)
  have hphase : (k : ℝ) / sqrt (d : ℝ) - ((2 * m : ℤ) : ℝ) =
      2 * (y - (m : ℝ)) := by
    dsimp [y]
    push_cast
    field_simp [hs.ne']
  have h := morse_normalized_phase_gap hd₀ hd hk (2 * m)
  rw [hphase, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  rw [inv_eq_one_div, show (k : ℝ) * (π / (2 * sqrt (d : ℝ))) = π * y by
    dsimp [y]; ring]
  exact h.trans (twice_distance_round_le_abs_sin_pi y)

/-- All candidate discrete levels are separated from zero by the integer
norm. This estimate does not assume the level classification. -/
theorem morse_discrete_level_gap {d j : ℕ} {A B : ℝ} (hd₀ : 0 < d)
    (hd : ¬ ∃ n : ℕ, n ^ 2 = d) (hj : 1 ≤ j) (hB : 0 < B)
    (hAB : sqrt A - 2 * sqrt B = (sqrt (d : ℝ))⁻¹)
    (m : ℕ) (hm : (m : ℝ) < ((j : ℝ) * sqrt A - 1) / 2) :
    sqrt B / (6 * sqrt (d : ℝ)) ≤ |Statements.morseLevel j A B m| := by
  let s := sqrt (d : ℝ)
  let t := sqrt B
  let κ : ℝ := ((j : ℝ) * sqrt A - 1) / 2 - m
  have hs : 0 < s := sqrt_pos.2 (by exact_mod_cast hd₀)
  have ht : 0 < t := sqrt_pos.2 hB
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (Nat.succ_le_iff.mp hj)
  have hκ : 0 < κ := sub_pos.mpr hm
  have ht₂ : t ^ 2 = B := sq_sqrt hB.le
  have hA : sqrt A = 2 * t + s⁻¹ := by change sqrt A - 2 * t = s⁻¹ at hAB; linarith
  have hdiff : (j : ℝ) * t - κ =
      -(((j : ℝ) / s - ((2 * (m : ℤ) + 1 : ℤ) : ℝ)) / 2) := by
    dsimp [κ]
    rw [hA, div_eq_mul_inv]
    push_cast
    ring
  have hnorm : 1 / (3 * (j : ℝ) * s) ≤
      |(j : ℝ) / s - ((2 * (m : ℤ) + 1 : ℤ) : ℝ)| :=
    morse_normalized_phase_gap hd₀ hd hj (2 * (m : ℤ) + 1)
  have hgap : 1 / (6 * (j : ℝ) * s) ≤ |(j : ℝ) * t - κ| := by
    rw [hdiff, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ = (1 / (3 * (j : ℝ) * s)) / 2 := by rw [div_div]; ring
      _ ≤ _ := div_le_div_of_nonneg_right hnorm (by norm_num)
  have hsum : 0 < (j : ℝ) * t + κ := add_pos (mul_pos hj₀ ht) hκ
  change t / (6 * s) ≤ |(j : ℝ) ^ 2 * B - κ ^ 2|
  rw [← ht₂, ← mul_pow, sq_sub_sq, abs_mul, abs_of_pos hsum, mul_comm ((j : ℝ) * t + κ)]
  calc
    _ = (1 / (6 * (j : ℝ) * s)) * ((j : ℝ) * t) := by
      field_simp [hj₀.ne', hs.ne']
    _ ≤ |(j : ℝ) * t - κ| * ((j : ℝ) * t) :=
      mul_le_mul_of_nonneg_right hgap (mul_nonneg hj₀.le ht.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hκ.le) (abs_nonneg _)

end ContinuousFlexibility.Radial
