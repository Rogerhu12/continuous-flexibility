import ContinuousFlexibility.Analysis.N04PositiveGeometryFiniteKernelBounds

/-!
# The exact original-state budget in an inverse partition

Selected identity slots are singleton state slots. All other blocks
carry the genuine inverse jets, each saving one spatial order. The
outer derivative and those blocks therefore pay the original spatial
order exactly once. The same split preserves one height factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

private theorem inversePartition_sums
    {ι : Type*} [DecidableEq ι] (s q : Finset ι) (hqs : q ⊆ s) :
    (s \ q).card + q.card = s.card ∧
      ∀ a : ι → ℕ, (∑ i ∈ s \ q, a i) + (∑ i ∈ q, a i) = ∑ i ∈ s, a i := by
  have hd : Disjoint (s \ q) q := by
    apply Finset.disjoint_left.mpr
    intro i hi hq
    exact (Finset.mem_sdiff.mp hi).2 hq
  have hu : (s \ q) ∪ q = s := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with h | h
      · exact (Finset.mem_sdiff.mp h).1
      · exact hqs h
    · intro hi
      by_cases hq : i ∈ q
      · exact Finset.mem_union.mpr (Or.inr hq)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hi, hq⟩))
  constructor
  · exact (Finset.card_union_of_disjoint hd).symm.trans (congrArg Finset.card hu)
  · intro a
    exact (Finset.sum_union hd).symm.trans (congrArg (fun z => ∑ i ∈ z, a i) hu)

/-- Removing exactly one order from every genuine inverse block and
from the outer positive jet gives the original total minus one. -/
theorem n04PositiveGeometry_inversePartition_cost
    {ι : Type*} [DecidableEq ι] (s q : Finset ι) (hqs : q ⊆ s)
    (hs : s.Nonempty) (κ β : ι → ℕ) (C : ℕ) (hC : 1 ≤ C)
    (hpositive : ∀ i ∈ s, 0 < κ i + β i)
    (hidentity : ∀ i ∈ q, κ i = 1 ∧ β i = 0) :
    ((s \ q).card + C * q.card - 1) +
        (∑ i ∈ s \ q, (β i + C * κ i - 1)) =
      (∑ i ∈ s, β i) + C * (∑ i ∈ s, κ i) - 1 := by
  have hsplit := inversePartition_sums s q hqs
  have hκ : (∑ i ∈ q, κ i) = q.card := by
    calc
      _ = ∑ _i ∈ q, (1 : ℕ) := Finset.sum_congr rfl (fun i hi => (hidentity i hi).1)
      _ = q.card := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hβ : (∑ i ∈ q, β i) = 0 := by
    exact Finset.sum_eq_zero (fun i hi => (hidentity i hi).2)
  have hblock (i : ι) (hi : i ∈ s \ q) : 1 ≤ β i + C * κ i := by
    have hp := hpositive i (Finset.mem_sdiff.mp hi).1
    have hm : κ i ≤ C * κ i := by
      simpa only [one_mul] using Nat.mul_le_mul_right (κ i) hC
    omega
  have hinner : (∑ i ∈ s \ q, (β i + C * κ i - 1)) + (s \ q).card =
      ∑ i ∈ s \ q, (β i + C * κ i) := by
    calc
      _ = ∑ i ∈ s \ q, ((β i + C * κ i - 1) + 1) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = _ := Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (hblock i hi))
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  have hqmul : q.card ≤ C * q.card := by
    simpa only [one_mul] using Nat.mul_le_mul_right q.card hC
  have houter : 1 ≤ (s \ q).card + C * q.card := by omega
  have htotal : (∑ i ∈ s, β i) + C * (∑ i ∈ s, κ i) =
      (∑ i ∈ s \ q, (β i + C * κ i)) + C * q.card := by
    rw [← hsplit.2 β, ← hsplit.2 κ, hκ, hβ,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [htotal]
  omega

/-- The original state count is the selected singleton count plus the
unselected block counts, so all positive-order height factors keep one
copy of the original height. -/
theorem n04PositiveGeometry_inversePartition_height
    {ι : Type*} [DecidableEq ι] (s q : Finset ι) (hqs : q ⊆ s)
    (κ : ι → ℕ) (hidentity : ∀ i ∈ q, κ i = 1)
    {H L : ℝ} (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) :
    parameterHeightWeight H q.card * (∏ i ∈ s \ q, parameterHeightWeight H (κ i)) ≤
      L ^ (s.card + 1) * parameterHeightWeight H (∑ i ∈ s, κ i) := by
  have hsplit := inversePartition_sums s q hqs
  have hκ : (∑ i ∈ q, κ i) = q.card := by
    calc
      _ = ∑ _i ∈ q, (1 : ℕ) := Finset.sum_congr rfl hidentity
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have htotal : q.card + (∑ i ∈ s \ q, κ i) = ∑ i ∈ s, κ i := by
    have h := hsplit.2 κ
    rw [hκ] at h
    omega
  have hp := n04PositiveGeometry_parameterHeightProduct_le (s \ q) κ hH hHL hL
  calc
    _ ≤ parameterHeightWeight H q.card *
        (L ^ (s \ q).card * parameterHeightWeight H (∑ i ∈ s \ q, κ i)) :=
      mul_le_mul_of_nonneg_left hp (parameterHeightWeight_nonneg hH _)
    _ = L ^ (s \ q).card * (parameterHeightWeight H q.card *
        parameterHeightWeight H (∑ i ∈ s \ q, κ i)) := by ring
    _ ≤ L ^ (s \ q).card * (L *
        parameterHeightWeight H (q.card + ∑ i ∈ s \ q, κ i)) :=
      mul_le_mul_of_nonneg_left (n01c_parameterHeightWeight_mul_le hH hHL hL _ _)
        (pow_nonneg (zero_le_one.trans hL) _)
    _ = L ^ ((s \ q).card + 1) * parameterHeightWeight H (∑ i ∈ s, κ i) := by
      rw [htotal, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hL (Nat.add_le_add_right (by omega) 1))
      (parameterHeightWeight_nonneg hH _)

end ContinuousFlexibility.Analysis
