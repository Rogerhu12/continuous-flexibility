import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Ring

/-!
# Iterated derivatives of a linear factor

The identity for the derivatives of `x * u x` is the algebraic input to
the one-dimensional division estimate.  It keeps the two nonzero terms
of the product rule explicit, without expanding a binomial sum.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

/-- Multiplication by the coordinate contributes exactly two terms to every
positive-order derivative. -/
theorem iteratedDeriv_succ_linearFactor {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (s : ℕ) (y : ℝ) :
    iteratedDeriv (s + 1) (fun x : ℝ => x * u x) y =
      y * iteratedDeriv (s + 1) u y + ((s + 1 : ℕ) : ℝ) * iteratedDeriv s u y := by
  have hd (n : ℕ) (x : ℝ) :
      HasDerivAt (iteratedDeriv n u) (iteratedDeriv (n + 1) u x) x := by
    have hn : Differentiable ℝ (iteratedDeriv n u) :=
      hu.differentiable_iteratedDeriv n
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
    simpa only [iteratedDeriv_succ] using (hn x).hasDerivAt
  induction s generalizing y with
  | zero =>
      simpa only [Nat.zero_add, Nat.cast_one, iteratedDeriv_zero, iteratedDeriv_one,
        one_mul, add_comm]
        using ((hasDerivAt_id' y).fun_mul (hd 0 y)).deriv
  | succ s ih =>
      have hfun : iteratedDeriv (s + 1) (fun x : ℝ => x * u x) =
          fun x : ℝ => x * iteratedDeriv (s + 1) u x +
            ((s + 1 : ℕ) : ℝ) * iteratedDeriv s u x :=
        funext ih
      have hstep := ((hasDerivAt_id y).mul (hd (s + 1) y)).add
        ((hd s y).const_mul ((s + 1 : ℕ) : ℝ))
      calc
        iteratedDeriv (s.succ + 1) (fun x : ℝ => x * u x) y =
            deriv (iteratedDeriv (s + 1) (fun x : ℝ => x * u x)) y := by
              rw [iteratedDeriv_succ]
        _ = 1 * iteratedDeriv (s + 1) u y +
              y * iteratedDeriv ((s + 1) + 1) u y +
              ((s + 1 : ℕ) : ℝ) * iteratedDeriv (s + 1) u y := by
                rw [hfun]
                exact hstep.deriv
        _ = y * iteratedDeriv (s.succ + 1) u y +
              ((s.succ + 1 : ℕ) : ℝ) * iteratedDeriv s.succ u y := by
                simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
                ring

/-- The same derivative identity, expressed using an arbitrary function
with a global smooth linear factorization. -/
theorem iteratedDeriv_succ_of_linearFactor {f u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hfactor : ∀ x : ℝ, f x = x * u x)
    (s : ℕ) (y : ℝ) :
    iteratedDeriv (s + 1) f y =
      y * iteratedDeriv (s + 1) u y + ((s + 1 : ℕ) : ℝ) * iteratedDeriv s u y := by
  have hf : f = fun x : ℝ => x * u x := funext hfactor
  rw [hf]
  exact iteratedDeriv_succ_linearFactor hu s y

end ContinuousFlexibility.Analysis
