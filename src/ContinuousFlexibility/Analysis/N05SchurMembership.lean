module

public import ContinuousFlexibility.Radial.WeightedSchurTest
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Schur estimates that establish membership in the output space

The scalar block bound controls every finite sum of squared output norms.
It therefore proves actual square summability before making a norm estimate;
no prior continuity or membership of the weighted output is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators ENNReal

/-- Finite output square sums are uniformly bounded by the same Schur
constant. The output sequence need not already be square summable. -/
theorem n05_schur_finite_square_bound
    (a : ℕ → ℕ → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k m, 0 ≤ a k m)
    (hrow : ∀ k, Summable (fun m => a k m) ∧ ∑' m, a k m ≤ A)
    (hcol : ∀ m, Summable (fun k => a k m) ∧ ∑' k, a k m ≤ B)
    (x y : ℕ → ℝ) (hx0 : ∀ m, 0 ≤ x m) (hy0 : ∀ k, 0 ≤ y k)
    (hx : Summable (fun m => x m ^ 2))
    (hy : ∀ k, y k ≤ ∑' m, a k m * x m) (q : Finset ℕ) :
    ∑ k ∈ q, y k ^ 2 ≤ A * B * ∑' m, x m ^ 2 := by
  let ξ : ℕ → ℝ := fun k => if k ∈ q then y k else 0
  have hξ0 (k : ℕ) : 0 ≤ ξ k := by
    dsimp only [ξ]
    split_ifs
    · exact hy0 k
    · exact le_rfl
  have hξ : Summable (fun k => ξ k ^ 2) :=
    summable_of_ne_finset_zero (s := q) (fun k hk => by simp [ξ, hk])
  obtain ⟨hsum, hschur⟩ := Radial.real_schur_test a hA hB ha hrow hcol
    ξ x hξ0 hx0 hξ hx
  have hξsum : (∑' k, ξ k ^ 2) = ∑ k ∈ q, y k ^ 2 := by
    rw [tsum_eq_sum (s := q) (fun k hk => by simp [ξ, hk])]
    exact Finset.sum_congr rfl (fun k hk => by simp only [ξ, if_pos hk])
  have htest : ∑ k ∈ q, y k ^ 2 ≤
      ∑' p : ℕ × ℕ, a p.1 p.2 * ξ p.1 * x p.2 := by
    rw [hsum.tsum_prod,
      tsum_eq_sum (s := q) (fun k hk => by simp [ξ, hk])]
    apply Finset.sum_le_sum
    intro k hk
    simp only [ξ, if_pos hk]
    calc
      y k ^ 2 = y k * y k := sq _
      _ ≤ y k * ∑' m, a k m * x m :=
        mul_le_mul_of_nonneg_left (hy k) (hy0 k)
      _ = ∑' m, a k m * y k * x m := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun m => by ring)
  have htotal := htest.trans hschur
  rw [hξsum] at htotal
  have hY : 0 ≤ ∑ k ∈ q, y k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hX : 0 ≤ ∑' m, x m ^ 2 := tsum_nonneg (fun m => sq_nonneg _)
  have hroot : Real.sqrt (∑ k ∈ q, y k ^ 2) ≤
      Real.sqrt (A * B) * Real.sqrt (∑' m, x m ^ 2) := by
    by_cases hz : Real.sqrt (∑ k ∈ q, y k ^ 2) = 0
    · rw [hz]
      positivity
    · have hp : 0 < Real.sqrt (∑ k ∈ q, y k ^ 2) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      apply le_of_mul_le_mul_right ?_ hp
      calc
        Real.sqrt (∑ k ∈ q, y k ^ 2) * Real.sqrt (∑ k ∈ q, y k ^ 2) =
            ∑ k ∈ q, y k ^ 2 := by rw [← sq, Real.sq_sqrt hY]
        _ ≤ Real.sqrt (A * B) * Real.sqrt (∑ k ∈ q, y k ^ 2) *
            Real.sqrt (∑' m, x m ^ 2) := htotal
        _ = _ := by ring
  calc
    ∑ k ∈ q, y k ^ 2 = Real.sqrt (∑ k ∈ q, y k ^ 2) ^ 2 :=
      (Real.sq_sqrt hY).symm
    _ ≤ (Real.sqrt (A * B) * Real.sqrt (∑' m, x m ^ 2)) ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hroot
    _ = _ := by rw [mul_pow, Real.sq_sqrt (mul_nonneg hA hB), Real.sq_sqrt hX]

/-- A block estimate proves membership in the genuine target Hilbert
sequence, including for dependent source and target fibers. -/
theorem n05_schur_memℓp
    {E F : ℕ → Type*} [∀ m, NormedAddCommGroup (E m)]
    [∀ k, NormedAddCommGroup (F k)]
    (a : ℕ → ℕ → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k m, 0 ≤ a k m)
    (hrow : ∀ k, Summable (fun m => a k m) ∧ ∑' m, a k m ≤ A)
    (hcol : ∀ m, Summable (fun k => a k m) ∧ ∑' k, a k m ≤ B)
    (x : lp E 2) (y : ∀ k, F k)
    (hy : ∀ k, ‖y k‖ ≤ ∑' m, a k m * ‖x m‖) : Memℓp y 2 := by
  have htwo : (2 : ENNReal).toReal = 2 := by norm_num
  have hx : Summable (fun m => ‖x m‖ ^ 2) := by
    simpa only [htwo, Real.rpow_two] using
      (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  apply memℓp_gen' (C := A * B * ∑' m, ‖x m‖ ^ 2)
  intro q
  simpa only [htwo, Real.rpow_two] using
    n05_schur_finite_square_bound a hA hB ha hrow hcol
      (fun m => ‖x m‖) (fun k => ‖y k‖) (fun m => norm_nonneg _)
      (fun k => norm_nonneg _) hx hy q

/-- Once the membership has been established, the very same block bound
gives the sharp product of the row and column Schur constants. -/
theorem n05_schur_lp_norm
    {E F : ℕ → Type*} [∀ m, NormedAddCommGroup (E m)]
    [∀ k, NormedAddCommGroup (F k)]
    (a : ℕ → ℕ → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k m, 0 ≤ a k m)
    (hrow : ∀ k, Summable (fun m => a k m) ∧ ∑' m, a k m ≤ A)
    (hcol : ∀ m, Summable (fun k => a k m) ∧ ∑' k, a k m ≤ B)
    (x : lp E 2) (y : lp F 2)
    (hy : ∀ k, ‖y k‖ ≤ ∑' m, a k m * ‖x m‖) :
    ‖y‖ ≤ Real.sqrt (A * B) * ‖x‖ := by
  have htwo : (2 : ENNReal).toReal = 2 := by norm_num
  have hx : Summable (fun m => ‖x m‖ ^ 2) := by
    simpa only [htwo, Real.rpow_two] using
      (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hnorm : (∑' m, ‖x m‖ ^ 2) = ‖x‖ ^ 2 := by
    simpa only [htwo, Real.rpow_two] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x).symm
  apply lp.norm_le_of_forall_sum_le (by norm_num) (by positivity)
  intro q
  simpa only [htwo, Real.rpow_two, mul_pow,
    Real.sq_sqrt (mul_nonneg hA hB), hnorm] using
    n05_schur_finite_square_bound a hA hB ha hrow hcol
      (fun m => ‖x m‖) (fun k => ‖y k‖) (fun m => norm_nonneg _)
      (fun k => norm_nonneg _) hx hy q

end ContinuousFlexibility.Analysis
