module

public import ContinuousFlexibility.Radial.WeightedSchurTest

/-!
# Square-sum form of the Schur test

The block application needs an output square-sum bound before that output
is known to lie in the weighted Hilbert space. This form proves both
summability and the bound from actual coordinate inequalities.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped ENNReal

theorem ennreal_schur_square_bound {ι κ : Type*}
    (a : ι → κ → ℝ≥0∞) (x : κ → ℝ≥0∞) {A B : ℝ≥0∞}
    (hrow : ∀ i, ∑' j, a i j ≤ A) (hcol : ∀ j, ∑' i, a i j ≤ B) :
    (∑' i, (∑' j, a i j * x j) ^ 2) ≤ A * B * ∑' j, x j ^ 2 := by
  have hsq (z : ℝ≥0∞) : (z ^ (1 / (2 : ℝ))) ^ 2 = z := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hprod (i : ι) (j : κ) :
      (a i j ^ (1 / (2 : ℝ))) *
        (a i j ^ (1 / (2 : ℝ)) * x j) = a i j * x j := by
    rw [← mul_assoc, ← pow_two, hsq]
  have hrowSq (i : ι) :
      (∑' j, a i j * x j) ^ 2 ≤ A * ∑' j, a i j * x j ^ 2 := by
    have hc := ennreal_cauchy_schwarz_tsum
      (fun j => a i j ^ (1 / (2 : ℝ)))
      (fun j => a i j ^ (1 / (2 : ℝ)) * x j)
    simp only [hprod, mul_pow, hsq] at hc
    exact hc.trans (mul_le_mul' (hrow i) le_rfl)
  calc
    (∑' i, (∑' j, a i j * x j) ^ 2) ≤
        ∑' i, A * ∑' j, a i j * x j ^ 2 := ENNReal.tsum_le_tsum hrowSq
    _ = A * ∑' i, ∑' j, a i j * x j ^ 2 := ENNReal.tsum_mul_left
    _ = A * ∑' j, ∑' i, a i j * x j ^ 2 := by rw [ENNReal.tsum_comm]
    _ = A * ∑' j, (∑' i, a i j) * x j ^ 2 := by
      congr 1
      exact tsum_congr (fun _ => ENNReal.tsum_mul_right)
    _ ≤ A * ∑' j, B * x j ^ 2 := by
      apply mul_le_mul' le_rfl
      exact ENNReal.tsum_le_tsum (fun j => mul_le_mul' (hcol j) le_rfl)
    _ = A * B * ∑' j, x j ^ 2 := by rw [ENNReal.tsum_mul_left]; ring

theorem schur_row_mul_summable {K : ℕ → ℕ → ℝ}
    (hK : ∀ k m, 0 ≤ K k m) (hrow : ∀ k, Summable (K k))
    {x : ℕ → ℝ} (hx : ∀ m, 0 ≤ x m) (hxs : Summable (fun m => x m ^ 2))
    (k : ℕ) : Summable (fun m => K k m * x m) := by
  have hb (m : ℕ) : x m ≤ Real.sqrt (∑' j, x j ^ 2) :=
    Real.le_sqrt_of_sq_le (hxs.le_tsum m (fun _ _ => sq_nonneg _))
  exact Summable.of_nonneg_of_le
    (fun m => mul_nonneg (hK k m) (hx m))
    (fun m => mul_le_mul_of_nonneg_left (hb m) (hK k m))
    ((hrow k).mul_right (Real.sqrt (∑' j, x j ^ 2)))

/-- Pointwise control by a Schur matrix implies actual square summability
of the output; it is not an assumption of this theorem. -/
theorem real_schur_square_bound (K : ℕ → ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : ∀ k m, 0 ≤ K k m)
    (hrow : ∀ k, Summable (K k) ∧ ∑' m, K k m ≤ A)
    (hcol : ∀ m, Summable (fun k => K k m) ∧ ∑' k, K k m ≤ B)
    (x y : ℕ → ℝ) (hx : ∀ m, 0 ≤ x m) (hy : ∀ k, 0 ≤ y k)
    (hxs : Summable (fun m => x m ^ 2))
    (hbound : ∀ k, y k ≤ ∑' m, K k m * x m) :
    Summable (fun k => y k ^ 2) ∧
      ∑' k, y k ^ 2 ≤ A * B * ∑' m, x m ^ 2 := by
  have hrowE : ∀ k, ∑' m, ENNReal.ofReal (K k m) ≤ ENNReal.ofReal A := by
    intro k
    rw [← ENNReal.ofReal_tsum_of_nonneg (hK k) (hrow k).1]
    exact ENNReal.ofReal_le_ofReal (hrow k).2
  have hcolE : ∀ m, ∑' k, ENNReal.ofReal (K k m) ≤ ENNReal.ofReal B := by
    intro m
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => hK k m) (hcol m).1]
    exact ENNReal.ofReal_le_ofReal (hcol m).2
  have hyE (k : ℕ) :
      ENNReal.ofReal (y k) ≤ ∑' m, ENNReal.ofReal (K k m) * ENNReal.ofReal (x m) := by
    have hs := schur_row_mul_summable hK (fun k => (hrow k).1) hx hxs k
    calc
      ENNReal.ofReal (y k) ≤ ENNReal.ofReal (∑' m, K k m * x m) :=
        ENNReal.ofReal_le_ofReal (hbound k)
      _ = ∑' m, ENNReal.ofReal (K k m * x m) :=
        ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (hK k m) (hx m)) hs
      _ = _ := tsum_congr (fun m => ENNReal.ofReal_mul (hK k m))
  have hX :
      (∑' m, ENNReal.ofReal (x m) ^ 2) = ENNReal.ofReal (∑' m, x m ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg (x m)) hxs]
    exact tsum_congr (fun m => (ENNReal.ofReal_pow (hx m) 2).symm)
  have hX0 : 0 ≤ ∑' m, x m ^ 2 := tsum_nonneg (fun _ => sq_nonneg _)
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hABX : 0 ≤ A * B * ∑' m, x m ^ 2 := mul_nonneg hAB hX0
  have hY :
      (∑' k, ENNReal.ofReal (y k ^ 2)) ≤
        ENNReal.ofReal (A * B * ∑' m, x m ^ 2) := by
    calc
      (∑' k, ENNReal.ofReal (y k ^ 2)) = ∑' k, ENNReal.ofReal (y k) ^ 2 :=
        tsum_congr (fun k => ENNReal.ofReal_pow (hy k) 2)
      _ ≤ ∑' k, (∑' m, ENNReal.ofReal (K k m) * ENNReal.ofReal (x m)) ^ 2 := by
        apply ENNReal.tsum_le_tsum
        intro k
        gcongr
        exact hyE k
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal B *
          ∑' m, ENNReal.ofReal (x m) ^ 2 :=
        ennreal_schur_square_bound (fun k m => ENNReal.ofReal (K k m))
          (fun m => ENNReal.ofReal (x m)) hrowE hcolE
      _ = ENNReal.ofReal (A * B * ∑' m, x m ^ 2) := by
        rw [hX, ENNReal.ofReal_mul hAB, ENNReal.ofReal_mul hA]
  have hYne : (∑' k, ENNReal.ofReal (y k ^ 2)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hY
  have hys : Summable (fun k => y k ^ 2) :=
    (ENNReal.summable_toReal hYne).congr (fun k => ENNReal.toReal_ofReal (sq_nonneg _))
  refine ⟨hys, ?_⟩
  have he : (∑' k, ENNReal.ofReal (y k ^ 2)).toReal = ∑' k, y k ^ 2 := by
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun k => ENNReal.toReal_ofReal (sq_nonneg _))
  simpa only [he] using ENNReal.toReal_le_of_le_ofReal hABX hY

end ContinuousFlexibility.Radial
