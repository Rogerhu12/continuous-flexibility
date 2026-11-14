module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Multiplication and cancellation of finite ordinary jets

The physical transmission argument differentiates the normal equation.
Leibniz's formula preserves equality of finite jets under multiplication.
If the coefficient is nonzero, equality of the product at the next order
then determines the next derivative from the already matching lower jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff BigOperators

/-- Multiplying two matching finite jets by the same smooth coefficient
preserves their equality at the prescribed order. -/
theorem iteratedDeriv_mul_eq_of_jets {a f g : ℝ → ℝ} {x : ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (hfg : ∀ i : ℕ, i ≤ n → iteratedDeriv i f x = iteratedDeriv i g x) :
    iteratedDeriv n (fun y => a y * f y) x =
      iteratedDeriv n (fun y => a y * g y) x := by
  change iteratedDeriv n (a * f) x = iteratedDeriv n (a * g) x
  rw [iteratedDeriv_mul (ha.contDiffAt.of_le (by simp)) (hf.contDiffAt.of_le (by simp)),
    iteratedDeriv_mul (ha.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [hfg (n - i) (Nat.sub_le n i)]

/-- A nonzero coefficient allows cancellation of the top derivative when
all lower derivatives have already been matched. -/
theorem iteratedDeriv_eq_of_mul_eq_of_lower_jets {a f g : ℝ → ℝ} {x : ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (ha0 : a x ≠ 0)
    (hfg : ∀ i : ℕ, i < n → iteratedDeriv i f x = iteratedDeriv i g x)
    (hprod : iteratedDeriv n (fun y => a y * f y) x =
      iteratedDeriv n (fun y => a y * g y) x) :
    iteratedDeriv n f x = iteratedDeriv n g x := by
  change iteratedDeriv n (a * f) x = iteratedDeriv n (a * g) x at hprod
  rw [iteratedDeriv_mul (ha.contDiffAt.of_le (by simp)) (hf.contDiffAt.of_le (by simp)),
    iteratedDeriv_mul (ha.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp)),
    Finset.sum_range_succ', Finset.sum_range_succ'] at hprod
  simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, Nat.sub_zero,
    one_mul] at hprod
  have htail :
      (∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ) *
        iteratedDeriv (i + 1) a x * iteratedDeriv (n - (i + 1)) f x) =
      ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ) *
        iteratedDeriv (i + 1) a x * iteratedDeriv (n - (i + 1)) g x := by
    apply Finset.sum_congr rfl
    intro i hi
    have hn : 0 < n := (Nat.zero_le i).trans_lt (Finset.mem_range.mp hi)
    rw [hfg (n - (i + 1)) (Nat.sub_lt hn (Nat.succ_pos i))]
  rw [htail] at hprod
  exact mul_left_cancel₀ ha0 (add_left_cancel hprod)

end ContinuousFlexibility.Analysis
