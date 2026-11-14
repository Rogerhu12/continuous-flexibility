module

public import ContinuousFlexibility.Analysis.N07aCircleBlockCoefficients

/-!
# Summable bounds for the actual multiplication blocks

Both cosine and sine inputs have the same summable coefficient tail.
Multiplication by the commutator frequency difference costs one more
ordinary angular derivative, with a fixed two-derivative summability loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n07aCosineScale_product_half_le (j l : ℕ) :
    n07aCosineScale j * n07aCosineScale l / 2 ≤ 2 := by
  have h := mul_le_mul (n07aCosineScale_le_two j) (n07aCosineScale_le_two l)
    (n07aCosineScale_nonneg l) (by norm_num : (0 : ℝ) ≤ 2)
  linarith

private theorem n07a_scaled_pair_abs_le (j l : ℕ) {x y X Y : ℝ}
    (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |(n07aCosineScale j * n07aCosineScale l / 2) * (x + y)| ≤ 2 * (X + Y) := by
  have ha : 0 ≤ n07aCosineScale j * n07aCosineScale l / 2 :=
    div_nonneg (mul_nonneg (n07aCosineScale_nonneg j) (n07aCosineScale_nonneg l)) (by norm_num)
  rw [abs_mul, abs_of_nonneg ha]
  exact (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hx hy)) ha).trans
    (mul_le_mul_of_nonneg_right (n07aCosineScale_product_half_le j l)
      (add_nonneg ((abs_nonneg _).trans hx) ((abs_nonneg _).trans hy)))

theorem n07aCosineMatrixEntry_abs_le {f : ℝ → ℝ} (hf : Continuous f) (l j : ℕ) :
    |n07aCosineMatrixEntry f l j| ≤
      2 * (‖circleFourierCoeff f ((j : ℤ) - l)‖ + ‖circleFourierCoeff f ((j : ℤ) + l)‖) := by
  rw [n07aCosineMatrixEntry_eq hf]
  exact n07a_scaled_pair_abs_le j l (n07aCosineAverage_abs_le hf _) (n07aCosineAverage_abs_le hf _)

theorem n07aSineMatrixEntry_abs_le {f : ℝ → ℝ} (hf : Continuous f) (l j : ℕ) :
    |n07aSineMatrixEntry f l j| ≤
      2 * (‖circleFourierCoeff f ((j : ℤ) - l)‖ + ‖circleFourierCoeff f ((j : ℤ) + l)‖) := by
  rw [n07aSineMatrixEntry_eq hf]
  exact n07a_scaled_pair_abs_le j l (n07aSineAverage_abs_le hf _) (n07aSineAverage_abs_le hf _)

theorem n07a_nat_frequency_sub_le_add (j l : ℕ) :
    |(((j : ℤ) - l : ℤ) : ℝ)| ≤ |(((j : ℤ) + l : ℤ) : ℝ)| := by
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
  rw [abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) + l)]
  exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) j],
    by linarith [Nat.cast_nonneg (α := ℝ) l]⟩

theorem n07aAngularTail_add_le_sub (j l : ℕ) :
    n07aAngularTail ((j : ℤ) + l) ≤ n07aAngularTail ((j : ℤ) - l) := by
  unfold n07aAngularTail
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (n07a_nat_frequency_sub_le_add j l)) 2

private theorem n07a_pair_tail_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (s : ℕ) {M₀ M : ℝ} (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M)
    (h₀ : ∀ θ, |f θ| ≤ M₀) (hs : ∀ θ, |iteratedDeriv (s + 2) f θ| ≤ M)
    (l j : ℕ) :
    (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s *
      (2 * (‖circleFourierCoeff f ((j : ℤ) - l)‖ +
        ‖circleFourierCoeff f ((j : ℤ) + l)‖)) ≤
      4 * (M₀ + M) * n07aAngularTail ((j : ℤ) - l) := by
  have hd := n07a_circleFourierCoeff_tail_le hf hp s hM₀ hM h₀ hs ((j : ℤ) - l)
  have hp₀ := n07a_circleFourierCoeff_tail_le hf hp s hM₀ hM h₀ hs ((j : ℤ) + l)
  have hp' : (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s *
      ‖circleFourierCoeff f ((j : ℤ) + l)‖ ≤
      (M₀ + M) * n07aAngularTail ((j : ℤ) - l) :=
    ((mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity)
        (add_le_add le_rfl (n07a_nat_frequency_sub_le_add j l)) s) (norm_nonneg _)).trans hp₀).trans
      (mul_le_mul_of_nonneg_left (n07aAngularTail_add_le_sub j l) (add_nonneg hM₀ hM))
  nlinarith only [hd, hp']

/-- The two actual parity blocks share one frequency tail. -/
theorem n07a_circleMatrix_weighted_bounds {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (s : ℕ) {M₀ M : ℝ} (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M)
    (h₀ : ∀ θ, |f θ| ≤ M₀) (hs : ∀ θ, |iteratedDeriv (s + 2) f θ| ≤ M)
    (l j : ℕ) :
    (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s * |n07aCosineMatrixEntry f l j| ≤
        4 * (M₀ + M) * n07aAngularTail ((j : ℤ) - l) ∧
    (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s * |n07aSineMatrixEntry f l j| ≤
        4 * (M₀ + M) * n07aAngularTail ((j : ℤ) - l) := by
  have htail := n07a_pair_tail_bound hf hp s hM₀ hM h₀ hs l j
  exact ⟨(mul_le_mul_of_nonneg_left (n07aCosineMatrixEntry_abs_le hf.continuous l j)
    (by positivity)).trans htail,
    (mul_le_mul_of_nonneg_left (n07aSineMatrixEntry_abs_le hf.continuous l j)
      (by positivity)).trans htail⟩

/-- The factor `l-j` in the actual Λ-commutator costs precisely one
additional coefficient derivative. -/
theorem n07a_circleMatrix_commutator_bounds {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (s : ℕ) {M₀ M : ℝ} (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M)
    (h₀ : ∀ θ, |f θ| ≤ M₀) (hs : ∀ θ, |iteratedDeriv (s + 3) f θ| ≤ M)
    (l j : ℕ) :
    (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s *
        |((l : ℝ) - j) * n07aCosineMatrixEntry f l j| ≤
        4 * (M₀ + M) * n07aAngularTail ((j : ℤ) - l) ∧
    (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s *
        |((l : ℝ) - j) * n07aSineMatrixEntry f l j| ≤
        4 * (M₀ + M) * n07aAngularTail ((j : ℤ) - l) := by
  have h := n07a_circleMatrix_weighted_bounds hf hp (s + 1) hM₀ hM h₀
    (by simpa only [Nat.add_assoc] using hs) l j
  have hd : |(l : ℝ) - j| = |(((j : ℤ) - l : ℤ) : ℝ)| := by
    simp only [Int.cast_sub, Int.cast_natCast]
    exact abs_sub_comm _ _
  have hstep (x : ℝ) :
      (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s * |((l : ℝ) - j) * x| ≤
        (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ (s + 1) * |x| := by
    rw [abs_mul, hd, pow_succ]
    nlinarith [mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1 +
      |(((j : ℤ) - l : ℤ) : ℝ)|) s) (abs_nonneg x)]
  exact ⟨(hstep _).trans h.1, (hstep _).trans h.2⟩

end ContinuousFlexibility.Analysis
