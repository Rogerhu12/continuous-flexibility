module

public import ContinuousFlexibility.Radial.R11bPartitionSquare
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.Linarith

/-!
# Weighted pointwise partition and index-fiber estimates

The first estimate uses only the finite overlap of the partition. The
second groups a finite family by its cell index before making any
estimate, so no uniform bound on the number of cells at one index is used.
-/

@[expose] public section

open Set
open scoped BigOperators

namespace ContinuousFlexibility.Radial

theorem profile_partition_weighted_square_le {ι : Type*}
    (χ : ι → ℝ) (z : ℝ) (w : ι → ℝ) {B : ℕ} {c K : ℝ}
    (hc : 0 ≤ c) (hfinite : (Function.support χ).Finite)
    (hcard : (Function.support χ).ncard ≤ B) (hsum : (∑' i, χ i) = 1)
    (hweight : ∀ i, χ i ≠ 0 → c ≤ K * w i) :
    c * z ^ 2 ≤ (B : ℝ) * K * ∑' i, w i * (χ i * z) ^ 2 := by
  have hfin₀ : (Function.support (fun i => (χ i * z) ^ 2)).Finite := by
    apply hfinite.subset
    intro i hi
    change χ i ≠ 0
    intro hz
    exact hi (by
      change (χ i * z) ^ 2 = 0
      simp only [hz, zero_mul, zero_pow (by decide : 2 ≠ 0)])
  have hfin₁ : (Function.support (fun i => w i * (χ i * z) ^ 2)).Finite := by
    apply hfinite.subset
    intro i hi
    change χ i ≠ 0
    intro hz
    exact hi (by
      change w i * (χ i * z) ^ 2 = 0
      simp only [hz, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero])
  have hs₀ : Summable (fun i => (χ i * z) ^ 2) := summable_of_hasFiniteSupport hfin₀
  have hs₁ : Summable (fun i => w i * (χ i * z) ^ 2) := summable_of_hasFiniteSupport hfin₁
  have hp (i : ι) : c * (χ i * z) ^ 2 ≤ K * (w i * (χ i * z) ^ 2) := by
    by_cases hi : χ i = 0
    · simp only [hi, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
    · calc
        _ ≤ (K * w i) * (χ i * z) ^ 2 :=
          mul_le_mul_of_nonneg_right (hweight i hi) (sq_nonneg _)
        _ = K * (w i * (χ i * z) ^ 2) := mul_assoc _ _ _
  have hcomp := Summable.tsum_le_tsum hp (hs₀.mul_left c) (hs₁.mul_left K)
  simp only [tsum_mul_left] at hcomp
  have hpart := r11b_partition_square_bound χ z hfinite hcard hsum
  rw [sq_abs] at hpart
  have hleft := mul_le_mul_of_nonneg_left hpart hc
  have hright := mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg B)
  nlinarith only [hleft, hright]

/-- A cell family is summed over each index fiber before its partition
square bound is applied. -/
theorem profile_finset_index_square_le (index : ℕ → ℕ) (s : Finset ℕ)
    (χ c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hχ : ∀ t : Finset ℕ, ∑ m ∈ t, χ m ^ 2 ≤ 1) :
    (∑ m ∈ s, c (index m) * χ m ^ 2) ≤ ∑ n ∈ s.image index, c n := by
  classical
  have hmap (m : ℕ) (hm : m ∈ s) : index m ∈ s.image index :=
    Finset.mem_image_of_mem index hm
  calc
    (∑ m ∈ s, c (index m) * χ m ^ 2) =
        ∑ n ∈ s.image index, ∑ m ∈ s with index m = n, c (index m) * χ m ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun m => c (index m) * χ m ^ 2)).symm
    _ ≤ ∑ n ∈ s.image index, c n := by
      apply Finset.sum_le_sum
      intro n _
      calc
        (∑ m ∈ s with index m = n, c (index m) * χ m ^ 2) =
            ∑ m ∈ s with index m = n, c n * χ m ^ 2 := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [(Finset.mem_filter.mp hm).2]
        _ = c n * ∑ m ∈ s with index m = n, χ m ^ 2 := by rw [Finset.mul_sum]
        _ ≤ c n * 1 := mul_le_mul_of_nonneg_left (hχ _) (hc n)
        _ = c n := mul_one _

end ContinuousFlexibility.Radial
