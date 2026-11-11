import ContinuousFlexibility.Analysis.N05ReferenceAngularJetBasis

/-!
# Dual high angular tests for all derivative orders

Differentiating the normalized derivative phase again gives the original
cosine with the exact sign and frequency power. These identities turn the
actual weak angular relation into coefficient identities without assuming
smoothness of the source.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

theorem n05_iteratedDeriv_comp (p q : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv p (iteratedDeriv q f) = iteratedDeriv (p + q) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem n05_referenceHighJetBasis_periodic (b n : ℕ) :
    Function.Periodic (n05_referenceHighJetBasis b n) (2 * Real.pi) := by
  induction b using Nat.twoStepInduction with
  | zero => exact r11b_cosineMode_periodic _
  | one => exact (r11b_sineMode_periodic _).neg
  | more b hb _ => exact hb.neg

theorem n05_referenceHighJetBasis_even_order (b n : ℕ) :
    n05_referenceHighJetBasis (2 * b) n =
      fun θ => (-1 : ℝ) ^ b * referenceAngularBasis (n + 2) θ := by
  induction b with
  | zero =>
    simp only [Nat.mul_zero, n05_referenceHighJetBasis, pow_zero, one_mul,
      referenceAngularBasis]
  | succ b hb =>
    rw [show 2 * (b + 1) = 2 * b + 2 by omega]
    funext θ
    simp only [n05_referenceHighJetBasis, hb, pow_succ]
    ring

theorem n05_referenceHighJetBasis_dual_derivative (b n : ℕ) :
    iteratedDeriv b (n05_referenceHighJetBasis b n) =
      fun θ => (-1 : ℝ) ^ b * (((2 * (n + 2) : ℕ) : ℝ) ^ b) *
        referenceAngularBasis (n + 2) θ := by
  funext θ
  have h := congrArg (fun v : ℝ → ℝ => iteratedDeriv b v θ)
    (n05_referenceHighBasis_iteratedDeriv b n)
  rw [n05_iteratedDeriv_comp, show b + b = 2 * b by omega,
    n05_referenceHighBasis_iteratedDeriv, n05_referenceHighJetBasis_even_order,
    iteratedDeriv_const_mul_field] at h
  have hc : (((2 * (n + 2) : ℕ) : ℝ) ^ b) ≠ 0 :=
    pow_ne_zero b (by positivity)
  apply mul_left_cancel₀ hc
  calc
    (((2 * (n + 2) : ℕ) : ℝ) ^ b) *
        iteratedDeriv b (n05_referenceHighJetBasis b n) θ =
      (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        ((-1 : ℝ) ^ b * referenceAngularBasis (n + 2) θ) := h.symm
    _ = _ := by
      rw [Nat.mul_comm 2 b, pow_mul]
      ring

end ContinuousFlexibility.Radial
