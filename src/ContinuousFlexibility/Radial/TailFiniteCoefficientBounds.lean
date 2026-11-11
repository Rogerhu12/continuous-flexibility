import ContinuousFlexibility.Radial.TailMassResistanceData
import Mathlib.Data.Finsupp.Basic

/-!
# Finite coefficient estimates for the low hats

Each coefficient meets at most two resistance gaps. The estimates here
sum both neighboring contributions without assumptions on the size or
location of the finite coefficient support.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

def tailCoefficientMass (T : DeepTailData) (a : ℕ →₀ ℝ) : ℝ :=
  ∑ n ∈ a.support, tailMass T n * a n ^ 2

theorem tailCoefficientMass_nonneg {T : DeepTailData} (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) : 0 ≤ tailCoefficientMass T a :=
  Finset.sum_nonneg (fun n _ => mul_nonneg (tailMass_pos hT n).le (sq_nonneg _))

theorem tailCoefficientMass_sum_le {T : DeepTailData} (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (s : Finset ℕ) :
    (∑ n ∈ s, tailMass T n * a n ^ 2) ≤ tailCoefficientMass T a := by
  calc
    _ ≤ ∑ n ∈ a.support ∪ s, tailMass T n * a n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (fun n _ _ => mul_nonneg (tailMass_pos hT n).le (sq_nonneg _))
    _ = tailCoefficientMass T a := by
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro n _ hn
      rw [Finsupp.notMem_support_iff.mp hn, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]

theorem tailCoefficientMass_shift_sum_le {T : DeepTailData} (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (s : Finset ℕ) :
    (∑ n ∈ s, tailMass T (n + 1) * a (n + 1) ^ 2) ≤ tailCoefficientMass T a := by
  calc
    _ = ∑ n ∈ s.image (fun n => n + 1), tailMass T n * a n ^ 2 := by
      rw [Finset.sum_image]
      intro n _ m _ h
      exact Nat.add_right_cancel h
    _ ≤ _ := tailCoefficientMass_sum_le hT a _

theorem tailCoefficientMass_single_le {T : DeepTailData} (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (n : ℕ) :
    tailMass T n * a n ^ 2 ≤ tailCoefficientMass T a := by
  simpa only [Finset.sum_singleton] using tailCoefficientMass_sum_le hT a {n}

theorem tailCoefficientMass_eq_range {T : DeepTailData} (a : ℕ →₀ ℝ) {N : ℕ}
    (ha : a.support ⊆ Finset.range N) :
    tailCoefficientMass T a = ∑ n ∈ Finset.range N, tailMass T n * a n ^ 2 := by
  apply Finset.sum_subset ha
  intro n _ hn
  rw [Finsupp.notMem_support_iff.mp hn, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]

theorem tail_finite_gap_mass_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (s : Finset ℕ) :
    (∑ n ∈ s, 2 * tailGapMass T n * (a n ^ 2 + a (n + 1) ^ 2)) ≤
      4 * T.η * tailCoefficientMass T a := by
  have hpoint : ∀ n, 2 * tailGapMass T n * (a n ^ 2 + a (n + 1) ^ 2) ≤
      2 * T.η * (tailMass T n * a n ^ 2 + tailMass T (n + 1) * a (n + 1) ^ 2) := by
    intro n
    have hl := mul_le_mul_of_nonneg_right (deepTail_gap_mass_le_left hT n)
      (sq_nonneg (a n))
    have hr := mul_le_mul_of_nonneg_right (deepTail_gap_mass_le_right hT n)
      (sq_nonneg (a (n + 1)))
    nlinarith
  calc
    _ ≤ ∑ n ∈ s, 2 * T.η *
        (tailMass T n * a n ^ 2 + tailMass T (n + 1) * a (n + 1) ^ 2) :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = 2 * T.η * ((∑ n ∈ s, tailMass T n * a n ^ 2) +
        ∑ n ∈ s, tailMass T (n + 1) * a (n + 1) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * T.η * (tailCoefficientMass T a + tailCoefficientMass T a) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (tailCoefficientMass_sum_le hT a s)
          (tailCoefficientMass_shift_sum_le hT a s))
        (mul_nonneg (by norm_num) hT.2.2.2.2.1.le)
    _ = _ := by ring

theorem tail_finite_gap_energy_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    {C : ℝ} (hC : 0 ≤ C) (a : ℕ →₀ ℝ) (s : Finset ℕ) :
    (∑ n ∈ s, 2 * (C / tailResistance T n) * (a n ^ 2 + a (n + 1) ^ 2)) ≤
      (4 * C * T.Λ / T.K) * tailCoefficientMass T a := by
  have hK : 0 < T.K := lt_trans zero_lt_one hT.2.2.2.2.2.2.1
  have hpoint : ∀ n, 2 * (C / tailResistance T n) * (a n ^ 2 + a (n + 1) ^ 2) ≤
      (2 * C * T.Λ / T.K) *
        (tailMass T n * a n ^ 2 + tailMass T (n + 1) * a (n + 1) ^ 2) := by
    intro n
    have hl := mul_le_mul_of_nonneg_left (deepTail_inverse_resistance_left hT n)
      (mul_nonneg hC (sq_nonneg (a n)))
    have hr := mul_le_mul_of_nonneg_left (deepTail_inverse_resistance_right hT n)
      (mul_nonneg hC (sq_nonneg (a (n + 1))))
    simp only [div_eq_mul_inv] at *
    nlinarith
  calc
    _ ≤ ∑ n ∈ s, (2 * C * T.Λ / T.K) *
        (tailMass T n * a n ^ 2 + tailMass T (n + 1) * a (n + 1) ^ 2) :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = (2 * C * T.Λ / T.K) * ((∑ n ∈ s, tailMass T n * a n ^ 2) +
        ∑ n ∈ s, tailMass T (n + 1) * a (n + 1) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (2 * C * T.Λ / T.K) *
        (tailCoefficientMass T a + tailCoefficientMass T a) := by
      apply mul_le_mul_of_nonneg_left
        (add_le_add (tailCoefficientMass_sum_le hT a s)
          (tailCoefficientMass_shift_sum_le hT a s))
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hT.2.2.1.le) hK.le
    _ = _ := by ring

end ContinuousFlexibility.Radial
