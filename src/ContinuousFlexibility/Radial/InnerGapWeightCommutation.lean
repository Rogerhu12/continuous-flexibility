module

public import ContinuousFlexibility.Radial.InnerWeightRatios
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact commutation of gap weights and the positive interface

Every cut is an endpoint of one positive gap. Assigning the geometric
mean of the two neighboring cell weights to that gap assigns the same
number at both endpoints. Consequently the weight commutes with the
whole gap flux block, including its off-diagonal entries. This proof is
independent of their size and applies simultaneously to either weight
sign.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A diagonal weight commutes with a matrix when every nonzero entry
connects two coordinates carrying the same weight. -/
theorem inner_diagonal_commute_of_support (w : ι → ℝ) (M : Matrix ι ι ℝ)
    (hweight : ∀ i j, M i j ≠ 0 → w i = w j) :
    Commute (Matrix.diagonal w) M := by
  apply (commute_iff_eq _ _).mpr
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : M i j = 0
  · rw [hij, mul_zero, zero_mul]
  · rw [hweight i j hij, mul_comm]

variable {β : Type*}

/-- Each gap has one geometric mean weight, used at all its cuts. Real
powers represent both signs without a second weight construction. -/
def innerGapWeightMatrix (gapOfCut : ι → β) (u v : β → ℝ) (σ : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (innerGeometricMeanWeight (u (gapOfCut i)) (v (gapOfCut i))) ^ σ)

theorem innerGapWeightMatrix_posDef (gapOfCut : ι → β) (u v : β → ℝ)
    (hu : ∀ b, 0 < u b) (hv : ∀ b, 0 < v b) (σ : ℝ) :
    (innerGapWeightMatrix gapOfCut u v σ).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  exact Real.rpow_pos_of_pos
    (innerGeometricMeanWeight_pos (hu (gapOfCut i)) (hv (gapOfCut i))) σ

/-- The negative sign is the canonical matrix inverse of the positive
sign, rather than an unrelated matrix with a separate estimate. -/
theorem innerGapWeightMatrix_inv (gapOfCut : ι → β) (u v : β → ℝ)
    (hu : ∀ b, 0 < u b) (hv : ∀ b, 0 < v b) :
    (innerGapWeightMatrix gapOfCut u v 1)⁻¹ = innerGapWeightMatrix gapOfCut u v (-1) := by
  apply Matrix.inv_eq_right_inv
  simp only [innerGapWeightMatrix, Real.rpow_one, Real.rpow_neg_one,
    Matrix.diagonal_mul_diagonal]
  have h : (fun i => innerGeometricMeanWeight (u (gapOfCut i)) (v (gapOfCut i)) *
      (innerGeometricMeanWeight (u (gapOfCut i)) (v (gapOfCut i)))⁻¹) =
      (fun _ : ι => (1 : ℝ)) := by
    funext i
    exact mul_inv_cancel₀ (innerGeometricMeanWeight_pos
      (hu (gapOfCut i)) (hv (gapOfCut i))).ne'
  rw [h, Matrix.diagonal_one]

/-- A full gap flux matrix commutes with the common endpoint weight; no
smallness condition is placed on a short gap's off-diagonal entries. -/
theorem innerGapWeightMatrix_commute_block (gapOfCut : ι → β) (u v : β → ℝ)
    (σ : ℝ) (b : β) (Λ : Matrix ι ι ℝ)
    (hsupport : ∀ i j, gapOfCut i ≠ b ∨ gapOfCut j ≠ b → Λ i j = 0) :
    Commute (innerGapWeightMatrix gapOfCut u v σ) Λ := by
  apply inner_diagonal_commute_of_support
  intro i j hij
  have hi : gapOfCut i = b := by
    by_contra h
    exact hij (hsupport i j (Or.inl h))
  have hj : gapOfCut j = b := by
    by_contra h
    exact hij (hsupport i j (Or.inr h))
  rw [hi, hj]

/-- The weight commutes with the actual algebraic reference interface
`diag κ + ∑ Λ`, while keeping every positive gap block intact. -/
theorem innerGapWeightMatrix_commute_reference [Fintype β]
    (gapOfCut : ι → β) (u v : β → ℝ) (σ : ℝ) (κ : ι → ℝ)
    (Λ : β → Matrix ι ι ℝ)
    (hsupport : ∀ b i j, gapOfCut i ≠ b ∨ gapOfCut j ≠ b → Λ b i j = 0) :
    Commute (innerGapWeightMatrix gapOfCut u v σ) (Matrix.diagonal κ + ∑ b, Λ b) := by
  have hdiag : Commute (innerGapWeightMatrix gapOfCut u v σ) (Matrix.diagonal κ) :=
    Matrix.commute_diagonal _ _
  have hgaps : Commute (innerGapWeightMatrix gapOfCut u v σ) (∑ b, Λ b) :=
    Commute.sum_right Finset.univ Λ _ (fun b _ =>
      innerGapWeightMatrix_commute_block gapOfCut u v σ b (Λ b) (hsupport b))
  exact hdiag.add_right hgaps

end ContinuousFlexibility.Radial
