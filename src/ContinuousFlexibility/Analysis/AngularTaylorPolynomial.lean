import ContinuousFlexibility.Analysis.BoundaryTaylorExtension
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual angular derivatives of a finite radial Taylor polynomial

Only the positive radial orders contribute to the difference from the
boundary angular derivative. Their uniform first angular-derivative
bound gives an error proportional to the chosen collar width.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_boundaryTaylorPolynomial_angle
    {n : ℕ} {A : ℕ → ℝ → ℝ}
    (hA : ∀ j ≤ n, ContDiff ℝ ∞ (A j)) (c r θ : ℝ) :
    HasDerivAt (fun η => boundaryTaylorPolynomial n c A (r, η))
      (boundaryTaylorPolynomial n c (fun j => deriv (A j)) (r, θ)) θ := by
  unfold boundaryTaylorPolynomial
  apply HasDerivAt.fun_sum
  intro j hj
  change HasDerivAt (fun η : ℝ => A j η / (j.factorial : ℝ) * (r - c) ^ j)
    (deriv (A j) θ / (j.factorial : ℝ) * (r - c) ^ j) θ
  exact (((hA j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).differentiable
    (by simp) θ).hasDerivAt.div_const (j.factorial : ℝ)).mul_const ((r - c) ^ j)

/-- Higher radial orders are small on a small collar, uniformly in the
angle and without any bound on the zeroth boundary coefficient. -/
theorem abs_boundaryTaylorPolynomial_sub_zero_le
    {n : ℕ} {A : ℕ → ℝ → ℝ} {c r θ δ M : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hM : 0 ≤ M) (hr : |r - c| ≤ δ)
    (hA : ∀ j, 0 < j → j ≤ n → |A j θ| ≤ M) :
    |boundaryTaylorPolynomial n c A (r, θ) - A 0 θ| ≤
      ((n + 1 : ℕ) : ℝ) * M * δ := by
  let s := (Finset.range (n + 1)).erase 0
  let f : ℕ → ℝ := fun j => A j θ / (j.factorial : ℝ) * (r - c) ^ j
  have hzero : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.succ_pos n)
  have he : boundaryTaylorPolynomial n c A (r, θ) - A 0 θ = ∑ j ∈ s, f j := by
    unfold boundaryTaylorPolynomial
    rw [← Finset.sum_erase_add (s := Finset.range (n + 1)) (f := f) hzero]
    simp only [f, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
    ring
  have hterm (j : ℕ) (hj : j ∈ s) : |f j| ≤ M * δ := by
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hj).2)
    have hpow : |r - c| ^ j ≤ δ := by
      cases j with
      | zero => exact (hj0 rfl).elim
      | succ j =>
          rw [pow_succ]
          have hp : |r - c| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg _) (hr.trans hδone)
          exact (mul_le_mul hp hr (abs_nonneg _) zero_le_one).trans_eq (one_mul δ)
    have hfact : (1 : ℝ) ≤ (j.factorial : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos j))
    have hfactpos : (0 : ℝ) < (j.factorial : ℝ) := zero_lt_one.trans_le hfact
    have hdiv : |A j θ| / (j.factorial : ℝ) ≤ M := by
      apply (div_le_iff₀ hfactpos).mpr
      calc
        _ ≤ M := hA j (Nat.pos_of_ne_zero hj0) hjn
        _ = M * 1 := (mul_one M).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hfact hM
    calc
      |f j| = (|A j θ| / (j.factorial : ℝ)) * |r - c| ^ j := by
        simp only [f, abs_mul, abs_div, abs_of_pos hfactpos, abs_pow]
      _ ≤ M * δ := mul_le_mul hdiv hpow (pow_nonneg (abs_nonneg _) _) hM
  have hcard : s.card ≤ n + 1 := by
    have hsub : s ⊆ Finset.range (n + 1) :=
      fun _ hj => (Finset.mem_erase.mp hj).2
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hcard' : (s.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [he]
  calc
    _ ≤ ∑ j ∈ s, |f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ s, M * δ := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * (M * δ) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n + 1 : ℕ) : ℝ) * (M * δ) :=
      mul_le_mul_of_nonneg_right hcard' (mul_nonneg hM hδ)
    _ = _ := by ring

/-- A degree-one lift at radial order zero and periodic higher radial
data give the same degree-one lift for the full polynomial. -/
theorem boundaryTaylorPolynomial_period_add
    {n : ℕ} {A : ℕ → ℝ → ℝ} {T : ℝ}
    (hzero : ∀ θ, A 0 (θ + T) = A 0 θ + T)
    (hperiod : ∀ j, 0 < j → j ≤ n → Function.Periodic (A j) T)
    (c r θ : ℝ) :
    boundaryTaylorPolynomial n c A (r, θ + T) =
      boundaryTaylorPolynomial n c A (r, θ) + T := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      A j (θ + T) / (j.factorial : ℝ) * (r - c) ^ j =
        A j θ / (j.factorial : ℝ) * (r - c) ^ j + if j = 0 then T else 0 := by
    by_cases hj0 : j = 0
    · subst j
      simp only [hzero θ, Nat.factorial_zero, Nat.cast_one, div_one,
        pow_zero, mul_one, ite_true]
    · have hp : A j (θ + T) = A j θ :=
        hperiod j (Nat.pos_of_ne_zero hj0) (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) θ
      simp only [hp, if_neg hj0, add_zero]
  unfold boundaryTaylorPolynomial
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        (A j θ / (j.factorial : ℝ) * (r - c) ^ j + if j = 0 then T else 0) :=
      Finset.sum_congr rfl hterm
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp

theorem boundaryTaylorPolynomial_reflect
    {n : ℕ} {A : ℕ → ℝ → ℝ}
    (hodd : ∀ j ≤ n, ∀ θ, A j (-θ) = -A j θ) (c r θ : ℝ) :
    boundaryTaylorPolynomial n c A (r, -θ) =
      -boundaryTaylorPolynomial n c A (r, θ) := by
  unfold boundaryTaylorPolynomial
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hodd j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) θ]
  ring

end ContinuousFlexibility.Analysis

