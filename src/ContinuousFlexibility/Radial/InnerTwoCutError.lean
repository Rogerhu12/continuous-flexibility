import ContinuousFlexibility.Radial.InnerInterfaceInverse
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# From the two cut entries to the Euclidean error norm

Compression estimates the entries of each normalized two-cut matrix.
The operator norm estimate below applies to arbitrary real entries,
including the nonsymmetric matrices produced by weight conjugation.
Its constant is independent of the number of pieces in the inner region.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped Matrix.Norms.L2Operator InnerProductSpace BigOperators

theorem innerTwoCutMatrix_norm_le (A : Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hA : ∀ i j, |A i j| ≤ η) : ‖A‖ ≤ 4 * η := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
  intro x y hx hy
  have hx' (i : Fin 2) : |x i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hx] using PiLp.norm_apply_le x i
  have hy' (i : Fin 2) : |y i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hy] using PiLp.norm_apply_le y i
  have hterm (i j : Fin 2) : y i * (A i j * x j) ≤ η := by
    apply (le_abs_self _).trans
    calc
      |y i * (A i j * x j)| = (|y i| * |A i j|) * |x j| := by
        rw [abs_mul, abs_mul]
        ring
      _ ≤ (1 * η) * 1 := mul_le_mul
        (mul_le_mul (hy' i) (hA i j) (abs_nonneg _) zero_le_one)
        (hx' j) (abs_nonneg _) (mul_nonneg zero_le_one hη)
      _ = η := by ring
  simp only [RCLike.re_to_real]
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith only [hterm 0 0, hterm 0 1, hterm 1 0, hterm 1 1]

def innerTwoCutWeightedError (κ W : Fin 2 → ℝ)
    (E : Matrix (Fin 2) (Fin 2) ℝ) (sign : Bool) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (if sign then W i / W j else W j / W i) *
    (E i j / Real.sqrt (κ i * κ j))

/-- A common two-sided cut-weight ratio estimate treats both conjugations
of the same actual error matrix, without any symmetry requirement. -/
theorem innerTwoCutWeightedError_norm_le (κ W : Fin 2 → ℝ)
    (E : Matrix (Fin 2) (Fin 2) ℝ) {R η : ℝ}
    (hW : ∀ i, 0 < W i) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hratio : ∀ i j, W i / W j ≤ R)
    (hentry : ∀ i j, |E i j / Real.sqrt (κ i * κ j)| ≤ η)
    (sign : Bool) : ‖innerTwoCutWeightedError κ W E sign‖ ≤ 4 * R * η := by
  have h := innerTwoCutMatrix_norm_le (innerTwoCutWeightedError κ W E sign)
    (mul_nonneg hR hη) (by
      intro i j
      dsimp only [innerTwoCutWeightedError]
      rw [abs_mul]
      apply mul_le_mul _ (hentry i j) (abs_nonneg _) hR
      cases sign with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [abs_of_pos (div_pos (hW j) (hW i))]
        exact hratio j i
      | true =>
        simp only [ite_true]
        rw [abs_of_pos (div_pos (hW i) (hW j))]
        exact hratio i j)
  simpa only [mul_assoc] using h

end ContinuousFlexibility.Radial
