import ContinuousFlexibility.Radial.MatchingMatrixAlgebra
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Inverting the normalized matrix of cut values

The Green-column argument produces a matrix `1 + E`.  This module isolates
the exact inverse identities and the elementary norm estimate used in the
Dirichlet correction.  It applies to any finite set of cuts.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The normalized cut matrix is invertible when its perturbation has
operator norm at most one half.  The inverse bound is in the actual sup
norm on the finite boundary-value space. -/
theorem positiveBufferMatrix_inverse_bound (E : Matrix n n ℝ)
    (hE : ∀ x : n → ℝ, ‖E *ᵥ x‖ ≤ (1 / 2 : ℝ) * ‖x‖) :
    IsUnit (1 + E).det ∧ ∀ y : n → ℝ, ‖(1 + E)⁻¹ *ᵥ y‖ ≤ 2 * ‖y‖ := by
  have h := matchingK_lower_bound (fun _ : n => (1 : ℝ)) (fun _ => 0)
    (fun _ => 1) E (1 + E) (by simp) 1 (by norm_num)
    (by intro i; norm_num) (by simpa using hE)
  simpa only [matchingK, Matrix.diagonal_one, Matrix.diagonal_zero, one_mul,
    sub_zero, div_one] using h.2

/-- First resolvent identity for the normalized cut matrix. -/
theorem positiveBufferMatrix_inverse_sub_one (E : Matrix n n ℝ)
    (hE : IsUnit (1 + E).det) :
    (1 + E)⁻¹ - 1 = -E * (1 + E)⁻¹ := by
  have hmul := Matrix.mul_nonsing_inv (1 + E) hE
  rw [add_mul, one_mul] at hmul
  calc
    (1 + E)⁻¹ - 1 = -(E * (1 + E)⁻¹) := by
      rw [← hmul]
      abel
    _ = -E * (1 + E)⁻¹ := by rw [neg_mul]

/-- The second-order identity retains attenuation at both ends of a
matrix entry.  Bounding the inverse by a constant does not lose either
of the two exterior exponential factors. -/
theorem positiveBufferMatrix_inverse_second_order (E : Matrix n n ℝ)
    (hE : IsUnit (1 + E).det) :
    (1 + E)⁻¹ - 1 = -E + E * (1 + E)⁻¹ * E := by
  let J : Matrix n n ℝ := (1 + E)⁻¹
  have hl : (1 + E) * J = 1 := Matrix.mul_nonsing_inv _ hE
  have hr : J * (1 + E) = 1 := Matrix.nonsing_inv_mul _ hE
  have hleft : E * J = 1 - J := by
    rw [add_mul, one_mul] at hl
    calc
      E * J = (J + E * J) - J := by abel
      _ = 1 - J := by rw [hl]
  have hright : J * E = 1 - J := by
    rw [mul_add, mul_one] at hr
    calc
      J * E = (J + J * E) - J := by abel
      _ = 1 - J := by rw [hr]
  change J - 1 = -E + E * J * E
  rw [hleft, sub_mul, one_mul, hright]
  abel

/-- A left inverse of the cut trace matrix gives the exact coefficients
which subtract all boundary values from a full-model solution. -/
theorem positiveBufferMatrix_cancel_cut_values (E : Matrix n n ℝ)
    (hE : IsUnit (1 + E).det) (z : n → ℝ) :
    z - (1 + E) *ᵥ ((1 + E)⁻¹ *ᵥ z) = 0 := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hE, Matrix.one_mulVec,
    sub_self]

/-- A zero-boundary homogeneous field has no nonzero cut-source
coefficients once the normalized cut matrix is invertible. -/
theorem positiveBufferMatrix_no_hidden_kernel (E : Matrix n n ℝ)
    (hE : IsUnit (1 + E).det) {z : n → ℝ}
    (hz : (1 + E) *ᵥ z = 0) : z = 0 := by
  have h := congrArg (fun x => (1 + E)⁻¹ *ᵥ x) hz
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE,
    Matrix.one_mulVec, Matrix.mulVec_zero] using h

end ContinuousFlexibility.Radial
