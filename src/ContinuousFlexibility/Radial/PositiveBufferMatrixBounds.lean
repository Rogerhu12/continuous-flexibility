module

public import ContinuousFlexibility.Radial.PositiveBufferMatrix
public import Mathlib.Tactic

/-!
# Two-sided weights in the inverse cut matrix

The inverse identity is estimated entry by entry. In particular, the error
keeps the small factor at each endpoint; a bound by the largest error alone
would not give the stated Dirichlet-to-Neumann estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Matrix Finset

theorem positiveBufferMatrix_mul_entry_bound {n : Type*} [Fintype n]
    (A B : Matrix n n ℝ) (u v s t : n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i)
    (hA : ∀ i j, |A i j| ≤ u i * v j)
    (hB : ∀ i j, |B i j| ≤ s i * t j) (i j : n) :
    |(A * B) i j| ≤ u i * t j * ∑ k, v k * s k := by
  calc
    |(A * B) i j| ≤ ∑ k, |A i k * B k j| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (u i * v k) * (s k * t j) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) (mul_nonneg (hu i) (hv k))
    _ = u i * t j * ∑ k, v k * s k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem positiveBuffer_two_weights (w : Fin 2 → ℝ) (i : Fin 2) :
    w i * (∑ j, w j) ≤ 2 * ∑ j, w j ^ 2 := by
  simp only [Fin.sum_univ_two]
  fin_cases i
  · change w 0 * (w 0 + w 1) ≤ 2 * (w 0 ^ 2 + w 1 ^ 2)
    nlinarith [sq_nonneg (w 0 - w 1), sq_nonneg (w 0), sq_nonneg (w 1)]
  · change w 1 * (w 0 + w 1) ≤ 2 * (w 0 ^ 2 + w 1 ^ 2)
    nlinarith [sq_nonneg (w 0 - w 1), sq_nonneg (w 0), sq_nonneg (w 1)]

theorem positiveBuffer_two_weights_sq (w : Fin 2 → ℝ) :
    (∑ j, w j) ^ 2 ≤ 2 * ∑ j, w j ^ 2 := by
  simp only [Fin.sum_univ_two]
  nlinarith [sq_nonneg (w 0 - w 1)]

/-- The rank-one entry bound gives a small operator in the actual sup norm
used for the finite matrix inverse. -/
theorem positiveBufferMatrix_weighted_operator_bound (E : Matrix (Fin 2) (Fin 2) ℝ)
    (w : Fin 2 → ℝ) {η : ℝ} (hη : 0 ≤ η) (hw : ∀ i, 0 ≤ w i)
    (hE : ∀ i j, |E i j| ≤ η * w i * w j)
    (hsmall : η * (∑ j, w j ^ 2) ≤ 1 / 4) :
    ∀ x : Fin 2 → ℝ, ‖E *ᵥ x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := by
  intro x
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  calc
    |(E *ᵥ x) i| ≤ ∑ j, |E i j * x j| := by
      change |∑ j, E i j * x j| ≤ ∑ j, |E i j * x j|
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (η * w i * w j) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hE i j)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
        (abs_nonneg _) (mul_nonneg (mul_nonneg hη (hw i)) (hw j))
    _ = η * (w i * (∑ j, w j)) * ‖x‖ := by
      simp only [Fin.sum_univ_two]
      ring
    _ ≤ η * (2 * ∑ j, w j ^ 2) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (positiveBuffer_two_weights w i) hη) (norm_nonneg x)
    _ ≤ (1 / 2 : ℝ) * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      nlinarith

/-- Operator control gives a uniform bound for each inverse entry. -/
theorem positiveBufferMatrix_inverse_entry_bound {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℝ)
    (hE : ∀ x : n → ℝ, ‖E *ᵥ x‖ ≤ (1 / 2 : ℝ) * ‖x‖) (i j : n) :
    |(1 + E)⁻¹ i j| ≤ 2 := by
  have h := (positiveBufferMatrix_inverse_bound E hE).2 (Pi.single j 1)
  have hi := norm_le_pi_norm ((1 + E)⁻¹ *ᵥ Pi.single j 1) i
  have hc : ‖((1 + E)⁻¹ *ᵥ Pi.single j 1) i‖ = |(1 + E)⁻¹ i j| := by
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Real.norm_eq_abs]
  rw [hc] at hi
  simpa only [Pi.norm_single, norm_one, mul_one] using hi.trans h

/-- Inversion preserves both endpoint weights, with a universal factor. -/
theorem positiveBufferMatrix_inverse_weighted_error (E : Matrix (Fin 2) (Fin 2) ℝ)
    (w : Fin 2 → ℝ) {η : ℝ} (hη : 0 ≤ η) (hw : ∀ i, 0 ≤ w i)
    (hE : ∀ i j, |E i j| ≤ η * w i * w j)
    (hsmall : η * (∑ j, w j ^ 2) ≤ 1 / 4) :
    IsUnit (1 + E).det ∧
      ∀ i j, |((1 + E)⁻¹ - 1) i j| ≤ 2 * η * w i * w j := by
  have hop := positiveBufferMatrix_weighted_operator_bound E w hη hw hE hsmall
  have hinv := (positiveBufferMatrix_inverse_bound E hop).1
  let J : Matrix (Fin 2) (Fin 2) ℝ := (1 + E)⁻¹
  have hJ : ∀ i j, |J i j| ≤ 2 := positiveBufferMatrix_inverse_entry_bound E hop
  have hsum : 0 ≤ ∑ k, w k := Finset.sum_nonneg (fun k _ => hw k)
  have hleft : ∀ i j, |(E * J) i j| ≤ (2 * η * w i * ∑ k, w k) * 1 := by
    intro i j
    have h := positiveBufferMatrix_mul_entry_bound E J (fun i => η * w i) w
      (fun _ => 2) (fun _ => 1) (fun i => mul_nonneg hη (hw i)) hw
      (fun _ => by norm_num) (fun _ => by norm_num) hE
      (fun i j => by simpa only [mul_one] using hJ i j) i j
    convert h using 1 <;> simp only [Fin.sum_univ_two] <;> ring
  have hdouble (i j : Fin 2) :
      |(E * J * E) i j| ≤ 4 * η ^ 2 * w i * w j * (∑ k, w k ^ 2) := by
    have h := positiveBufferMatrix_mul_entry_bound (E * J) E
      (fun i => 2 * η * w i * ∑ k, w k) (fun _ => 1) (fun k => η * w k) w
      (fun i => by have hi := hw i; positivity) (fun _ => by norm_num)
      (fun k => mul_nonneg hη (hw k)) hw hleft hE i j
    have h' : |(E * J * E) i j| ≤ 2 * η ^ 2 * w i * w j * (∑ k, w k) ^ 2 := by
      convert h using 1 <;> simp only [Fin.sum_univ_two] <;> ring
    calc
      _ ≤ 2 * η ^ 2 * w i * w j * (∑ k, w k) ^ 2 := h'
      _ ≤ 2 * η ^ 2 * w i * w j * (2 * ∑ k, w k ^ 2) := by
        apply mul_le_mul_of_nonneg_left (positiveBuffer_two_weights_sq w)
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg η)) (hw i)) (hw j)
      _ = _ := by ring
  refine ⟨hinv, ?_⟩
  intro i j
  rw [positiveBufferMatrix_inverse_second_order E hinv]
  change |-E i j + (E * J * E) i j| ≤ _
  calc
    _ ≤ |E i j| + |(E * J * E) i j| := by simpa only [abs_neg] using abs_add_le (-E i j) _
    _ ≤ η * w i * w j + 4 * η ^ 2 * w i * w j * (∑ k, w k ^ 2) :=
      add_le_add (hE i j) (hdouble i j)
    _ ≤ 2 * η * w i * w j := by
      have h := mul_le_mul_of_nonneg_left hsmall
        (show 0 ≤ 4 * η * w i * w j from
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hη) (hw i)) (hw j))
      nlinarith

end ContinuousFlexibility.Radial
