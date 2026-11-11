import ContinuousFlexibility.Radial.TailContinuedFraction

/-!
# The square-summable natural node solution

The limiting ratios from finite Dirichlet walls determine a positive
solution of the sign-alternated tridiagonal node equation. The mass-weighted
values decay geometrically under the deep-tail ratio bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter

private def tailPositiveNodes (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => r n * tailPositiveNodes r n

/-- Exact positive node recurrence and weighted square summability for the
natural line, in the sign-alternated coordinates of the node equation. -/
theorem exists_tailNaturalNodeLine {b c μ : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hc : ∀ n, 0 < c n) (hμ : ∀ n, 0 < μ n)
    (hε : ∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8))
    (hr : ∀ n, Real.sqrt (μ (n + 1)) * (c n / b (n + 1)) ≤
      (1 / 4 : ℝ) * Real.sqrt (μ n)) :
    let ε : ℕ → ℝ := fun n => c n ^ 2 / (b n * b (n + 1))
    ∃ y : ℕ → ℝ,
      y 0 = 1 ∧ (∀ n, 0 < y n) ∧
      (∀ n, y (n + 1) / y n = c n / b (n + 1) * tailFractionLimit ε hε n) ∧
      (∀ n, b (n + 1) * y (n + 1) = c n * y n + c (n + 1) * y (n + 2)) ∧
      (∀ n, Real.sqrt (μ (n + 1)) * y (n + 1) ≤
        (1 / 2 : ℝ) * (Real.sqrt (μ n) * y n)) ∧
      Summable (fun n => μ n * y n ^ 2) := by
  dsimp only
  let ε : ℕ → ℝ := fun n => c n ^ 2 / (b n * b (n + 1))
  let t := tailFractionLimit ε hε
  let r : ℕ → ℝ := fun n => c n / b (n + 1) * t n
  let y := tailPositiveNodes r
  have hy (n : ℕ) : y (n + 1) = r n * y n := rfl
  have ht (n : ℕ) : t n ∈ Icc 1 2 := tailFractionLimit_mem ε hε n
  have hypos (n : ℕ) : 0 < y n := by
    induction n with
    | zero => change 0 < (1 : ℝ); norm_num
    | succ n ih =>
      rw [hy]
      exact mul_pos (mul_pos (div_pos (hc n) (hb (n + 1))) (zero_lt_one.trans_le (ht n).1)) ih
  have hrec (n : ℕ) : b (n + 1) * y (n + 1) = c n * y n + c (n + 1) * y (n + 2) := by
    let den := 1 - ε (n + 1) * t (n + 1)
    have hεn : ε (n + 1) ∈ Icc 0 (1 / 8) := hε (n + 1)
    have hprod : ε (n + 1) * t (n + 1) ≤ (1 / 8 : ℝ) * 2 :=
      mul_le_mul hεn.2 (ht (n + 1)).2 (zero_le_one.trans (ht (n + 1)).1) (by norm_num)
    have hden : 0 < den := by dsimp only [den]; linarith only [hprod]
    have hfrac : t n = den⁻¹ := tailFractionLimit_eq_step ε hε n
    have htprod : t n * den = 1 := by rw [hfrac, inv_mul_cancel₀ hden.ne']
    have hsplit : t n = 1 + ε (n + 1) * t (n + 1) * t n := by
      dsimp only [den] at htprod
      linarith only [htprod]
    have hnext : y (n + 2) = c (n + 1) / b (n + 2) * t (n + 1) * y (n + 1) :=
      hy (n + 1)
    have hcur : y (n + 1) = c n / b (n + 1) * t n * y n := hy n
    calc
      b (n + 1) * y (n + 1) = (c n * y n) * t n := by
        rw [hcur]
        field_simp [(hb (n + 1)).ne']
      _ = c n * y n + (c n * y n) * (ε (n + 1) * t (n + 1) * t n) := by
        nth_rw 1 [hsplit]
        ring
      _ = c n * y n + c (n + 1) * y (n + 2) := by
        rw [hnext, hcur]
        dsimp only [ε]
        field_simp [(hb (n + 1)).ne', (hb (n + 2)).ne']
  let Y : ℕ → ℝ := fun n => Real.sqrt (μ n) * y n
  have hYpos (n : ℕ) : 0 ≤ Y n := mul_nonneg (Real.sqrt_nonneg _) (hypos n).le
  have hYstep (n : ℕ) : Y (n + 1) ≤ (1 / 2 : ℝ) * Y n := by
    change Real.sqrt (μ (n + 1)) * y (n + 1) ≤ (1 / 2 : ℝ) * Y n
    rw [hy]
    calc
      _ = (Real.sqrt (μ (n + 1)) * (c n / b (n + 1)) * t n) * y n := by dsimp only [r]; ring
      _ ≤ ((1 / 4 : ℝ) * Real.sqrt (μ n) * 2) * y n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hr n) (ht n).2 (zero_le_one.trans (ht n).1)
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))) (hypos n).le
      _ = _ := by dsimp only [Y]; ring
  have hYgeo (n : ℕ) : Y n ≤ (1 / 2 : ℝ) ^ n * Y 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ ≤ (1 / 2 : ℝ) * Y n := hYstep n
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * Y 0) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ']; ring
  refine ⟨y, rfl, hypos, ?_, hrec, hYstep, ?_⟩
  · intro n
    rw [hy, mul_div_cancel_right₀ _ (hypos n).ne']
  · have hs := (summable_geometric_of_lt_one (r := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)).mul_right (Y 0 ^ 2)
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hμ n).le (sq_nonneg _)) ?_ hs
    intro n
    have hsq : Y n ^ 2 ≤ ((1 / 2 : ℝ) ^ n * Y 0) ^ 2 :=
      pow_le_pow_left₀ (hYpos n) (hYgeo n) _
    have hmass : Y n ^ 2 = μ n * y n ^ 2 := by
      dsimp only [Y]
      rw [mul_pow, Real.sq_sqrt (hμ n).le]
    rw [hmass, mul_pow, ← pow_mul, mul_comm n 2, pow_mul] at hsq
    norm_num at hsq
    exact hsq

end ContinuousFlexibility.Radial
