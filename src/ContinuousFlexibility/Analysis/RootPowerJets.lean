module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Derivatives of the real power used in a root coordinate

The scalar derivative formula is valid for mathlib's ordinary derivatives
on the whole real line. At a positive argument it gives the precise scale
of every jet. The finite collection of coefficients can then be bounded
uniformly at any prescribed derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff BigOperators

/-- Falling-product coefficient in the derivative of a real power. -/
def rpowJetCoefficient (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => rpowJetCoefficient p n * (p - n)

/-- The ordinary iterated derivatives of a real power, with their exact
falling-product coefficients. -/
theorem iteratedDeriv_rpow_eq (p : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => y ^ p) x =
      rpowJetCoefficient p n * x ^ (p - n) := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero, rpowJetCoefficient, Nat.cast_zero, sub_zero, one_mul]
  | succ n ih =>
      have hfun : iteratedDeriv n (fun y : ℝ => y ^ p) =
          fun y : ℝ => rpowJetCoefficient p n * y ^ (p - n) := funext ih
      rw [iteratedDeriv_succ, hfun, deriv_const_mul_field, Real.deriv_rpow_const]
      simp only [rpowJetCoefficient, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      rw [show p - (n : ℝ) - 1 = p - ((n : ℝ) + 1) by ring]
      ring

/-- At a positive argument, the jet has the root value times one inverse
power of the argument for each differentiation. -/
theorem norm_iteratedDeriv_rpow_of_pos (p : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv n (fun y : ℝ => y ^ p) x‖ =
      ‖rpowJetCoefficient p n‖ * x ^ p / x ^ n := by
  rw [iteratedDeriv_rpow_eq, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),
    Real.rpow_sub hx, Real.rpow_natCast]
  ring

/-- The finitely many falling-product coefficients up to any fixed order
have one positive bound, at least one. -/
theorem exists_rpowJetCoefficient_bound (p : ℝ) (s : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, i ≤ s → ‖rpowJetCoefficient p i‖ ≤ D := by
  let D : ℝ := 1 + ∑ i ∈ Finset.range (s + 1), ‖rpowJetCoefficient p i‖
  have hsum : 0 ≤ ∑ i ∈ Finset.range (s + 1), ‖rpowJetCoefficient p i‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨D, by dsimp only [D]; linarith, ?_⟩
  intro i hi
  have hterm : ‖rpowJetCoefficient p i‖ ≤
      ∑ j ∈ Finset.range (s + 1), ‖rpowJetCoefficient p j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (rpowJetCoefficient p j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  dsimp only [D]
  linarith

end ContinuousFlexibility.Analysis
