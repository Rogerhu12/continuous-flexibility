import ContinuousFlexibility.Analysis.AngularFrequency
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The actual derivative-jet weight and the angular spectral weight

For period `π`, the `n`th Fourier mode has derivative frequency `2 n`.
The prescribed jet norm sums the squares of derivatives through order
`s`. Its exact squared weight is therefore the finite geometric sum
below, rather than a single Japanese-bracket power. The estimates here
compare increments in that actual norm to the existing angular Sobolev
norm, with constants independent of the base order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

def n07aAngularFrequencySquare (n : ℕ) : ℝ := (2 * (n : ℝ)) ^ 2

def n07aAngularJetWeightSq (s n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), n07aAngularFrequencySquare n ^ j

theorem n07aAngularFrequencySquare_nonneg (n : ℕ) :
    0 ≤ n07aAngularFrequencySquare n := sq_nonneg _

theorem n07aAngularFrequencySquare_two_le {n : ℕ} (hn : 1 ≤ n) :
    2 ≤ n07aAngularFrequencySquare n := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold n07aAngularFrequencySquare
  nlinarith

theorem n07aAngularJetWeightSq_zero_order (n : ℕ) : n07aAngularJetWeightSq 0 n = 1 := by
  simp only [n07aAngularJetWeightSq, zero_add, Finset.sum_range_one, pow_zero]

theorem n07aAngularJetWeightSq_succ (s n : ℕ) :
    n07aAngularJetWeightSq (s + 1) n =
      n07aAngularJetWeightSq s n + n07aAngularFrequencySquare n ^ (s + 1) := by
  exact Finset.sum_range_succ (fun j => n07aAngularFrequencySquare n ^ j) (s + 1)

theorem n07aAngularJetWeightSq_nonneg (s n : ℕ) : 0 ≤ n07aAngularJetWeightSq s n :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg (n07aAngularFrequencySquare_nonneg n) _)

theorem n07aAngularJetWeightSq_one_le (s n : ℕ) : 1 ≤ n07aAngularJetWeightSq s n := by
  have h := Finset.single_le_sum
    (s := Finset.range (s + 1)) (f := fun j => n07aAngularFrequencySquare n ^ j)
    (fun j _ => pow_nonneg (n07aAngularFrequencySquare_nonneg n) j)
    (show 0 ∈ Finset.range (s + 1) by simp)
  simpa only [pow_zero, n07aAngularJetWeightSq] using h

theorem n07aAngularJetWeightSq_top_le (s n : ℕ) :
    n07aAngularFrequencySquare n ^ s ≤ n07aAngularJetWeightSq s n :=
  Finset.single_le_sum
    (fun j _ => pow_nonneg (n07aAngularFrequencySquare_nonneg n) j)
    (Finset.mem_range.mpr (Nat.lt_succ_self s))

theorem n07aAngularJetWeightSq_zero_frequency (s : ℕ) :
    n07aAngularJetWeightSq s 0 = 1 := by
  induction s with
  | zero => exact n07aAngularJetWeightSq_zero_order 0
  | succ s ih =>
    rw [n07aAngularJetWeightSq_succ, ih]
    simp [n07aAngularFrequencySquare]

/-- At nonzero angular frequencies, the last derivative controls the whole jet. -/
theorem n07aAngularJetWeightSq_le_two_top (s : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    n07aAngularJetWeightSq s n ≤ 2 * n07aAngularFrequencySquare n ^ s := by
  induction s with
  | zero => rw [n07aAngularJetWeightSq_zero_order, pow_zero]; norm_num
  | succ s ih =>
    rw [n07aAngularJetWeightSq_succ, pow_succ]
    have ha := n07aAngularFrequencySquare_two_le hn
    have hp := pow_nonneg (n07aAngularFrequencySquare_nonneg n) s
    nlinarith

/-- The shifted derivative block is a subsum of the larger actual jet norm. -/
theorem n07aAngularJetWeightSq_shift_le (b p n : ℕ) :
    n07aAngularFrequencySquare n ^ p * n07aAngularJetWeightSq b n ≤
      n07aAngularJetWeightSq (b + p) n := by
  have he : n07aAngularJetWeightSq (b + p) n =
      (∑ j ∈ Finset.range p, n07aAngularFrequencySquare n ^ j) +
        n07aAngularFrequencySquare n ^ p * n07aAngularJetWeightSq b n := by
    unfold n07aAngularJetWeightSq
    rw [show b + p + 1 = p + (b + 1) by omega, Finset.sum_range_add]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact pow_add _ _ _
  rw [he]
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg (fun _ _ => pow_nonneg (n07aAngularFrequencySquare_nonneg n) _))

/-- A spectral Sobolev increment is bounded by the prescribed higher jet. -/
theorem n07aAngularJetWeightSq_lower (b p n : ℕ) :
    (1 + (n : ℝ) ^ 2) ^ p * n07aAngularJetWeightSq b n ≤
      n07aAngularJetWeightSq (b + p) n := by
  by_cases hn : n = 0
  · subst n
    simp only [n07aAngularJetWeightSq_zero_frequency, Nat.cast_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, one_pow, mul_one, le_refl]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have ha : 1 + (n : ℝ) ^ 2 ≤ n07aAngularFrequencySquare n := by
      unfold n07aAngularFrequencySquare
      nlinarith
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) ha p) (n07aAngularJetWeightSq_nonneg b n)).trans
      (n07aAngularJetWeightSq_shift_le b p n)

/-- The reverse comparison costs a fixed factor `2 * 4^p`, independent of `b`. -/
theorem n07aAngularJetWeightSq_upper (b p n : ℕ) :
    n07aAngularJetWeightSq (b + p) n ≤
      2 * 4 ^ p * (1 + (n : ℝ) ^ 2) ^ p * n07aAngularJetWeightSq b n := by
  by_cases hn : n = 0
  · subst n
    simp only [n07aAngularJetWeightSq_zero_frequency, Nat.cast_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, one_pow, mul_one]
    have hpow : (1 : ℝ) ≤ 4 ^ p := one_le_pow₀ (by norm_num)
    linarith
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have ha : n07aAngularFrequencySquare n ≤ 4 * (1 + (n : ℝ) ^ 2) := by
      unfold n07aAngularFrequencySquare
      nlinarith
    have hpow : n07aAngularFrequencySquare n ^ p ≤ 4 ^ p * (1 + (n : ℝ) ^ 2) ^ p := by
      simpa only [mul_pow] using
        pow_le_pow_left₀ (n07aAngularFrequencySquare_nonneg n) ha p
    calc
      n07aAngularJetWeightSq (b + p) n ≤ 2 * n07aAngularFrequencySquare n ^ (b + p) :=
        n07aAngularJetWeightSq_le_two_top (b + p) hn1
      _ = 2 * n07aAngularFrequencySquare n ^ p * n07aAngularFrequencySquare n ^ b := by
        rw [pow_add]
        ring
      _ ≤ 2 * (4 ^ p * (1 + (n : ℝ) ^ 2) ^ p) * n07aAngularJetWeightSq b n := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num))
          (n07aAngularJetWeightSq_top_le b n)
          (pow_nonneg (n07aAngularFrequencySquare_nonneg n) b) (by positivity)
      _ = _ := by ring

theorem n07aAngularJetWeightSq_lower_spectral (b p n : ℕ) :
    angularWeight n ^ (2 * p) * n07aAngularJetWeightSq b n ≤
      n07aAngularJetWeightSq (b + p) n := by
  simpa only [pow_mul, angularWeight_sq] using n07aAngularJetWeightSq_lower b p n

theorem n07aAngularJetWeightSq_upper_spectral (b p n : ℕ) :
    n07aAngularJetWeightSq (b + p) n ≤
      2 * 4 ^ p * angularWeight n ^ (2 * p) * n07aAngularJetWeightSq b n := by
  simpa only [pow_mul, angularWeight_sq] using n07aAngularJetWeightSq_upper b p n

end ContinuousFlexibility.Analysis
