module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Products of one-step node decay estimates

The interval product retains the individual edge factors, as required by
the localized tail Green estimate.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

/-- Iterating a one-step bound gives the exact finite product occurring in
the localized kernel estimate. -/
theorem tailNode_ratio_le_prod {y r : ℕ → ℝ}
    (hy : ∀ k, 0 < y k) (hr : ∀ k, 0 ≤ r k)
    (hstep : ∀ k, y (k + 1) ≤ r k * y k) {m n : ℕ} (hmn : m ≤ n) :
    y n / y m ≤ ∏ k ∈ Finset.Ico m n, r k := by
  have hmul : y n ≤ y m * ∏ k ∈ Finset.Ico m n, r k := by
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.prod_Ico_succ_top hn]
      calc
        y (n + 1) ≤ r n * y n := hstep n
        _ ≤ r n * (y m * ∏ k ∈ Finset.Ico m n, r k) :=
          mul_le_mul_of_nonneg_left ih (hr n)
        _ = y m * ((∏ k ∈ Finset.Ico m n, r k) * r n) := by ring
  exact (div_le_iff₀ (hy m)).mpr (hmul.trans_eq (mul_comm _ _))

end ContinuousFlexibility.Radial
