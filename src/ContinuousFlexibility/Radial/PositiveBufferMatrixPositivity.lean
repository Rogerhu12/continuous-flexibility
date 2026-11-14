module

public import ContinuousFlexibility.Radial.PositiveBufferMatrixBounds

/-!
# Positivity of the physical conormal matrix

The entrywise estimate controls the entire quadratic form. Rescaling by
the positive endpoint energies then yields strict physical positivity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Matrix Finset

theorem positiveBuffer_two_weighted_cauchy (w z : Fin 2 → ℝ) :
    (∑ i, w i * |z i|) ^ 2 ≤ (∑ i, w i ^ 2) * (∑ i, z i ^ 2) := by
  simp only [Fin.sum_univ_two]
  nlinarith [sq_nonneg (w 0 * |z 1| - w 1 * |z 0|), sq_abs (z 0), sq_abs (z 1)]

theorem positiveBufferMatrix_weighted_quadratic_bound
    (E : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hw : ∀ i, 0 ≤ w i)
    (hE : ∀ i j, |E i j| ≤ η * w i * w j) (z : Fin 2 → ℝ) :
    |∑ i, ∑ j, z i * E i j * z j| ≤
      η * (∑ i, w i ^ 2) * (∑ i, z i ^ 2) := by
  calc
    |∑ i, ∑ j, z i * E i j * z j| ≤
        ∑ i, |∑ j, z i * E i j * z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |z i * E i j * z j| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |z i| * (η * w i * w j) * |z j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
    _ = η * (∑ i, w i * |z i|) ^ 2 := by
      simp only [Fin.sum_univ_two]
      ring
    _ ≤ η * ((∑ i, w i ^ 2) * (∑ i, z i ^ 2)) :=
      mul_le_mul_of_nonneg_left (positiveBuffer_two_weighted_cauchy w z) hη
    _ = _ := by ring

theorem positiveBuffer_two_sq_pos {z : Fin 2 → ℝ} (hz : z ≠ 0) :
    0 < ∑ i, z i ^ 2 := by
  simp only [Fin.sum_univ_two]
  have h0 := sq_nonneg (z 0)
  have h1 := sq_nonneg (z 1)
  by_contra hn
  have he0 : z 0 = 0 := by nlinarith
  have he1 : z 1 = 0 := by nlinarith
  apply hz
  ext i
  fin_cases i
  · exact he0
  · exact he1

theorem positiveBufferMatrix_positive_perturbation
    (E : Matrix (Fin 2) (Fin 2) ℝ) (w d : Fin 2 → ℝ)
    {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ)
    (hw : ∀ i, 0 ≤ w i) (hd : ∀ i, δ ≤ d i)
    (hE : ∀ i j, |E i j| ≤ η * w i * w j)
    (hsmall : η * (∑ i, w i ^ 2) ≤ δ / 2)
    (z : Fin 2 → ℝ) (hz : z ≠ 0) :
    0 < ∑ i, ∑ j, z i * (Matrix.diagonal d + E) i j * z j := by
  have hsq := positiveBuffer_two_sq_pos hz
  have herr := positiveBufferMatrix_weighted_quadratic_bound E w hη hw hE z
  have hbound : |∑ i, ∑ j, z i * E i j * z j| ≤ δ / 2 * ∑ i, z i ^ 2 :=
    herr.trans (mul_le_mul_of_nonneg_right hsmall hsq.le)
  have hdiag : δ * (∑ i, z i ^ 2) ≤ ∑ i, d i * z i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hd i) (sq_nonneg _)
  have heq : (∑ i, ∑ j, z i * (Matrix.diagonal d + E) i j * z j) =
      (∑ i, d i * z i ^ 2) + ∑ i, ∑ j, z i * E i j * z j := by
    simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.diagonal_apply,
      Fin.zero_ne_one, (show (1 : Fin 2) ≠ 0 by decide), if_true, if_false]
    ring
  rw [heq]
  have hleft := (abs_le.mp hbound).1
  have hpos : 0 < δ * (∑ i, z i ^ 2) := mul_pos hδ hsq
  linarith

theorem positiveBufferMatrix_rescale_positive (M : Matrix (Fin 2) (Fin 2) ℝ)
    (s : Fin 2 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hM : ∀ z : Fin 2 → ℝ, z ≠ 0 →
      0 < ∑ i, ∑ j, z i * M i j * z j)
    (z : Fin 2 → ℝ) (hz : z ≠ 0) :
    0 < ∑ i, ∑ j, z i * (s i * M i j * s j) * z j := by
  let y : Fin 2 → ℝ := fun i => s i * z i
  have hy : y ≠ 0 := by
    intro heq
    apply hz
    ext i
    have hi := congrFun heq i
    exact (mul_eq_zero.mp hi).resolve_left (hs i)
  have h := hM y hy
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [y]
  ring

end ContinuousFlexibility.Radial
