module

public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Differential equations of the existing Hermite polynomials

These are mathlib's probabilists' Hermite polynomials, mapped to real
coefficients. Their derivative and second-order equation are deduced from
the existing recursion; no polynomial eigen-equation is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Polynomial
open scoped ContDiff

theorem derivative_integerHermite_succ (n : ℕ) :
    derivative (Polynomial.hermite (n + 1)) = C (↑(n + 1) : ℤ) * Polynomial.hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      derivative (Polynomial.hermite (n + 1 + 1)) =
          Polynomial.hermite (n + 1) + X * derivative (Polynomial.hermite (n + 1)) -
            derivative (derivative (Polynomial.hermite (n + 1))) := by
        rw [Polynomial.hermite_succ (n + 1), derivative_sub, derivative_mul]
        simp
      _ = Polynomial.hermite (n + 1) + X * (C (↑(n + 1) : ℤ) * Polynomial.hermite n) -
          C (↑(n + 1) : ℤ) * derivative (Polynomial.hermite n) := by
        simp only [ih, derivative_mul, derivative_C, zero_mul, zero_add]
      _ = C (↑(n + 1 + 1) : ℤ) * Polynomial.hermite (n + 1) := by
        rw [Polynomial.hermite_succ n]
        simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
        ring

theorem integerHermite_differentialEquation (n : ℕ) :
    derivative (derivative (Polynomial.hermite n)) - X * derivative (Polynomial.hermite n) +
      C (n : ℤ) * Polynomial.hermite n = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [derivative_integerHermite_succ,
      derivative_mul, derivative_C, zero_mul, zero_add]
    rw [Polynomial.hermite_succ n]
    ring

def hermitePolynomial (n : ℕ) : ℝ[X] :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

@[simp] theorem hermitePolynomial_zero : hermitePolynomial 0 = 1 := by
  simp [hermitePolynomial]

theorem hermitePolynomial_monic (n : ℕ) : (hermitePolynomial n).Monic :=
  Polynomial.Monic.map (Int.castRingHom ℝ) (Polynomial.hermite_monic n)

theorem hermitePolynomial_ne_zero (n : ℕ) : hermitePolynomial n ≠ 0 :=
  (hermitePolynomial_monic n).ne_zero

theorem hermitePolynomial_differentialEquation (n : ℕ) :
    derivative (derivative (hermitePolynomial n)) - X * derivative (hermitePolynomial n) +
      C (n : ℝ) * hermitePolynomial n = 0 := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) (integerHermite_differentialEquation n)
  simpa [hermitePolynomial, derivative_map] using h

theorem hermitePolynomial_differentialEquation_eval (n : ℕ) (x : ℝ) :
    (hermitePolynomial n).derivative.derivative.eval x =
      x * (hermitePolynomial n).derivative.eval x - (n : ℝ) * (hermitePolynomial n).eval x := by
  have h := congrArg (Polynomial.eval x) (hermitePolynomial_differentialEquation n)
  simp only [eval_add, eval_sub, eval_mul, eval_X, eval_C, eval_zero] at h
  linarith

end ContinuousFlexibility.Radial
