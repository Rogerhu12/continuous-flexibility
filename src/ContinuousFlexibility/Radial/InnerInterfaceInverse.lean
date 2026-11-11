import ContinuousFlexibility.Analysis.NeumannPackage
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# The weighted inverse of the inner interface matrix

This is the finite-dimensional inversion step of Lemma 6.3 of
`paper/flexible-surface-readable/06-global-reference-inverse.tex`.
The matrix norm is the operator norm on Euclidean space, for an arbitrary
finite set of cuts. The positive gap blocks remain part of `S₀`.

A small normalized error for either invertible weight proves that the
single matrix `S₀ + E` is invertible. Its canonical matrix inverse has the
stated Neumann factorization for every weight satisfying that estimate.
In particular the two signs use the same inverse and require no additional
unweighted smallness assumption. The local estimates which establish
smallness are separate from this algebraic step.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Analysis
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive inverse square root used to normalize the interface energy. -/
def innerInterfaceInverseSqrt (S₀ : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  CFC.sqrt S₀⁻¹

/-- Normalization uses the full positive interface matrix, including the gaps. -/
theorem innerInterfaceInverseSqrt_normalizes (S₀ : Matrix ι ι ℝ)
    (hS₀ : S₀.PosDef) :
    innerInterfaceInverseSqrt S₀ * S₀ * innerInterfaceInverseSqrt S₀ = 1 := by
  simpa only [innerInterfaceInverseSqrt, CFC.conjSqrt_apply,
    ← Matrix.nonsing_inv_eq_ringInverse] using
    CFC.conjSqrt_ringInverse_self S₀ hS₀.isStrictlyPositive

/-- The normalized weighted error of the interface matrix. -/
def innerInterfaceWeightedError (S₀ Ω E : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  innerInterfaceInverseSqrt S₀ * (Ω * E * Ω⁻¹) * innerInterfaceInverseSqrt S₀

/-- The Neumann inverse, transported without a norm loss from Euclidean space. -/
def innerInterfaceNeumann (R : Matrix ι ι ℝ) (hR : ‖R‖ < 1 / 2) : Matrix ι ι ℝ :=
  Matrix.toEuclideanCLM.symm
    (neumannInverse (Matrix.toEuclideanCLM R) (by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      exact hR.trans (by norm_num)))

theorem innerInterfaceNeumann_mul (R : Matrix ι ι ℝ) (hR : ‖R‖ < 1 / 2) :
    innerInterfaceNeumann R hR * (1 + R) = 1 := by
  apply Matrix.toEuclideanCLM.injective
  simp only [map_mul, map_add, map_one, innerInterfaceNeumann,
    StarAlgEquiv.apply_symm_apply]
  exact neumannInverse_mul _ _

theorem mul_innerInterfaceNeumann (R : Matrix ι ι ℝ) (hR : ‖R‖ < 1 / 2) :
    (1 + R) * innerInterfaceNeumann R hR = 1 := by
  apply Matrix.toEuclideanCLM.injective
  simp only [map_mul, map_add, map_one, innerInterfaceNeumann,
    StarAlgEquiv.apply_symm_apply]
  exact mul_neumannInverse _ _

theorem norm_innerInterfaceNeumann_le_two (R : Matrix ι ι ℝ)
    (hR : ‖R‖ < 1 / 2) : ‖innerInterfaceNeumann R hR‖ ≤ 2 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  simp only [innerInterfaceNeumann, StarAlgEquiv.apply_symm_apply]
  apply norm_neumannInverse_le_two
  simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hR.le

/-- Commutation of the cut weights with the positive gap blocks gives the
identity to which the Neumann construction applies. -/
theorem innerInterface_weighted_normalization (S₀ Ω E : Matrix ι ι ℝ)
    (hS₀ : S₀.PosDef) (hΩ : IsUnit Ω) (hcomm : Commute Ω S₀) :
    innerInterfaceInverseSqrt S₀ * (Ω * (S₀ + E) * Ω⁻¹) *
        innerInterfaceInverseSqrt S₀ = 1 + innerInterfaceWeightedError S₀ Ω E := by
  have hΩdet : IsUnit Ω.det := (Matrix.isUnit_iff_isUnit_det Ω).mp hΩ
  have hbase : Ω * S₀ * Ω⁻¹ = S₀ := by
    rw [hcomm.eq, mul_assoc, Matrix.mul_nonsing_inv Ω hΩdet, mul_one]
  calc
    innerInterfaceInverseSqrt S₀ * (Ω * (S₀ + E) * Ω⁻¹) *
        innerInterfaceInverseSqrt S₀ =
      innerInterfaceInverseSqrt S₀ * (Ω * S₀ * Ω⁻¹) *
          innerInterfaceInverseSqrt S₀ + innerInterfaceWeightedError S₀ Ω E := by
      dsimp only [innerInterfaceWeightedError]
      noncomm_ring
    _ = 1 + innerInterfaceWeightedError S₀ Ω E := by
      rw [hbase, innerInterfaceInverseSqrt_normalizes S₀ hS₀]

/-- A single weighted error estimate proves invertibility and the exact
factorization of the same canonical inverse. Positivity of the weight is
not needed for this algebraic step; any invertible commuting weight works. -/
theorem innerInterface_inverse_of_weighted_small (S₀ Ω E : Matrix ι ι ℝ)
    (hS₀ : S₀.PosDef) (hΩ : IsUnit Ω) (hcomm : Commute Ω S₀)
    (hsmall : ‖innerInterfaceWeightedError S₀ Ω E‖ < 1 / 2) :
    IsUnit (S₀ + E) ∧
      Ω * (S₀ + E)⁻¹ * Ω⁻¹ =
        innerInterfaceInverseSqrt S₀ *
          innerInterfaceNeumann (innerInterfaceWeightedError S₀ Ω E) hsmall *
            innerInterfaceInverseSqrt S₀ ∧
      ‖innerInterfaceNeumann (innerInterfaceWeightedError S₀ Ω E) hsmall‖ ≤ 2 := by
  let J : Matrix ι ι ℝ := innerInterfaceInverseSqrt S₀
  let B : Matrix ι ι ℝ := Ω * (S₀ + E) * Ω⁻¹
  let N : Matrix ι ι ℝ :=
    innerInterfaceNeumann (innerInterfaceWeightedError S₀ Ω E) hsmall
  have hnormalized : J * B * J = 1 + innerInterfaceWeightedError S₀ Ω E :=
    innerInterface_weighted_normalization S₀ Ω E hS₀ hΩ hcomm
  have hright : (1 + innerInterfaceWeightedError S₀ Ω E) * N = 1 :=
    mul_innerInterfaceNeumann _ hsmall
  have hnormalizedUnit : IsUnit (J * B * J) := by
    rw [hnormalized]
    exact isUnit_iff_exists_inv.mpr ⟨N, hright⟩
  have hJBunit : IsUnit (J * B) := isUnit_of_mul_isUnit_left hnormalizedUnit
  have hJunit : IsUnit J := isUnit_of_mul_isUnit_left hJBunit
  have hBunit : IsUnit B := isUnit_of_mul_isUnit_right hJBunit
  have hSunit : IsUnit (S₀ + E) :=
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hBunit)
  have hBinv : B⁻¹ = J * N * J := by
    apply Matrix.inv_eq_right_inv
    apply hJunit.mul_left_cancel
    calc
      J * (B * (J * N * J)) = (J * B * J) * N * J := by
        noncomm_ring
      _ = J := by rw [hnormalized, hright, one_mul]
      _ = J * 1 := (mul_one J).symm
  have hΩdet : IsUnit Ω.det := (Matrix.isUnit_iff_isUnit_det Ω).mp hΩ
  have hconjugate : B⁻¹ = Ω * (S₀ + E)⁻¹ * Ω⁻¹ := by
    dsimp only [B]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv Ω hΩdet]
    exact (mul_assoc Ω (S₀ + E)⁻¹ Ω⁻¹).symm
  exact ⟨hSunit, hconjugate.symm.trans hBinv,
    norm_innerInterfaceNeumann_le_two _ hsmall⟩

/-- Both weight signs, represented once. -/
def innerInterfaceWeight (Ω : Matrix ι ι ℝ) (forward : Bool) : Matrix ι ι ℝ :=
  if forward then Ω else Ω⁻¹

theorem isUnit_innerInterfaceWeight (Ω : Matrix ι ι ℝ) (hΩ : IsUnit Ω)
    (forward : Bool) : IsUnit (innerInterfaceWeight Ω forward) := by
  cases forward with
  | false => exact Matrix.isUnit_nonsing_inv_iff.mpr hΩ
  | true => exact hΩ

theorem innerInterfaceWeight_commute (S₀ Ω : Matrix ι ι ℝ) (hΩ : IsUnit Ω)
    (hcomm : Commute Ω S₀) (forward : Bool) :
    Commute (innerInterfaceWeight Ω forward) S₀ := by
  cases forward with
  | true => exact hcomm
  | false =>
    have hΩdet : IsUnit Ω.det := (Matrix.isUnit_iff_isUnit_det Ω).mp hΩ
    apply hΩ.mul_left_cancel
    calc
      Ω * (Ω⁻¹ * S₀) = S₀ := by
        rw [← mul_assoc, Matrix.mul_nonsing_inv Ω hΩdet, one_mul]
      _ = S₀ * (Ω * Ω⁻¹) := by rw [Matrix.mul_nonsing_inv Ω hΩdet, mul_one]
      _ = (S₀ * Ω) * Ω⁻¹ := (mul_assoc S₀ Ω Ω⁻¹).symm
      _ = (Ω * S₀) * Ω⁻¹ := by rw [hcomm.eq]
      _ = Ω * (S₀ * Ω⁻¹) := mul_assoc Ω S₀ Ω⁻¹

/-- The two signs give factorizations of one inverse, with a middle factor
bounded by two for each sign. There is no unweighted smallness premise. -/
theorem innerInterface_inverse_both_weights (S₀ Ω E : Matrix ι ι ℝ)
    (hS₀ : S₀.PosDef) (hΩ : Ω.PosDef) (hcomm : Commute Ω S₀)
    (hsmall : ∀ forward : Bool,
      ‖innerInterfaceWeightedError S₀ (innerInterfaceWeight Ω forward) E‖ < 1 / 2) :
    IsUnit (S₀ + E) ∧ ∀ forward : Bool,
      innerInterfaceWeight Ω forward * (S₀ + E)⁻¹ *
          (innerInterfaceWeight Ω forward)⁻¹ =
        innerInterfaceInverseSqrt S₀ *
          innerInterfaceNeumann
            (innerInterfaceWeightedError S₀ (innerInterfaceWeight Ω forward) E)
            (hsmall forward) * innerInterfaceInverseSqrt S₀ ∧
      ‖innerInterfaceNeumann
        (innerInterfaceWeightedError S₀ (innerInterfaceWeight Ω forward) E)
        (hsmall forward)‖ ≤ 2 := by
  have hfirst := innerInterface_inverse_of_weighted_small S₀
    (innerInterfaceWeight Ω true) E hS₀
    (isUnit_innerInterfaceWeight Ω hΩ.isUnit true)
    (innerInterfaceWeight_commute S₀ Ω hΩ.isUnit hcomm true) (hsmall true)
  refine ⟨hfirst.1, fun forward => ?_⟩
  exact (innerInterface_inverse_of_weighted_small S₀
    (innerInterfaceWeight Ω forward) E hS₀
    (isUnit_innerInterfaceWeight Ω hΩ.isUnit forward)
    (innerInterfaceWeight_commute S₀ Ω hΩ.isUnit hcomm forward) (hsmall forward)).2

end ContinuousFlexibility.Radial
