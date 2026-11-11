import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Pointwise square control for a partition with bounded overlap

Finite Cauchy--Schwarz controls the square of a field by the sum of the
squares of its localized pieces. The bound uses the number of nonzero
localizers at the point, without a bound on the number of cells at a level.
The result also holds for signed localizers whose sum is one.
-/

namespace ContinuousFlexibility.Radial

open scoped BigOperators

/-- Finite Cauchy--Schwarz with an upper bound on the number of terms. -/
theorem r11b_finset_sum_square_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    {B : ℕ} (hcard : s.card ≤ B) :
    (∑ i ∈ s, a i) ^ 2 ≤ (B : ℝ) * ∑ i ∈ s, a i ^ 2 := by
  have hcs : (∑ i ∈ s, a i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, a i ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      (Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ι => (1 : ℝ)) a)
  exact hcs.trans (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hcard) (Finset.sum_nonneg (fun i _ => sq_nonneg (a i))))

/-- A finite partition of one reconstructs a scalar with square loss at most
the overlap bound. Nonnegativity of the partition is not needed. -/
theorem r11b_finset_partition_square_bound {ι : Type*}
    (s : Finset ι) (χ : ι → ℝ) (z : ℝ) {B : ℕ}
    (hsum : (∑ i ∈ s, χ i) = 1) (hcard : s.card ≤ B) :
    |z| ^ 2 ≤ (B : ℝ) * ∑ i ∈ s, (χ i * z) ^ 2 := by
  have hsum_mul : (∑ i ∈ s, χ i * z) = z := by
    rw [← Finset.sum_mul, hsum, one_mul]
  simpa only [hsum_mul, sq_abs] using
    (r11b_finset_sum_square_le s (fun i => χ i * z) hcard)

/-- The pointwise estimate in the form used by a countable radial partition.
Its right side is a genuine finite sum expressed as a `tsum`, so it can be
integrated by Tonelli after multiplication by a nonnegative physical weight. -/
theorem r11b_partition_square_bound {ι : Type*} (χ : ι → ℝ) (z : ℝ)
    {B : ℕ} (hfinite : (Function.support χ).Finite)
    (hcard : (Function.support χ).ncard ≤ B)
    (hsum : (∑' i, χ i) = 1) :
    |z| ^ 2 ≤ (B : ℝ) * ∑' i, (χ i * z) ^ 2 := by
  classical
  let s : Finset ι := hfinite.toFinset
  have hzero (i : ι) (hi : i ∉ s) : χ i = 0 := by
    by_contra h
    exact hi (hfinite.mem_toFinset.mpr h)
  have hsum' : (∑ i ∈ s, χ i) = 1 :=
    (tsum_eq_sum (f := χ) (s := s) hzero).symm.trans hsum
  have hcard' : s.card ≤ B := by
    change hfinite.toFinset.card ≤ B
    rw [← Set.ncard_eq_toFinset_card (Function.support χ) hfinite]
    exact hcard
  have hsq : (∑' i, (χ i * z) ^ 2) = ∑ i ∈ s, (χ i * z) ^ 2 :=
    tsum_eq_sum (s := s) (fun i hi => by simp [hzero i hi])
  rw [hsq]
  exact r11b_finset_partition_square_bound s χ z hsum' hcard'

end ContinuousFlexibility.Radial
