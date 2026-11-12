import ContinuousFlexibility.Analysis.N01cBoundsRestriction

/-! Combine the zero-radial and positive-radial parameter estimates without
moving the common controlling order inside the parameter quantifier. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

private theorem flowPrefix_weight_mono
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    {base high high' : ℕ} {B B' H E : ℝ}
    (hhigh : high ≤ high') (hB : 0 ≤ B) (hBB' : B ≤ B')
    (hH : 0 ≤ H) (hE : 1 ≤ E) (x : X) {j : ℕ} (v : Fin j → X) :
    B * H ^ (3 / 4 : ℝ) * E ^ B * oneHighVariationWeight p base high x v ≤
      B' * H ^ (3 / 4 : ℝ) * E ^ B' * oneHighVariationWeight p base high' x v := by
  have hHpow := Real.rpow_nonneg hH (3 / 4 : ℝ)
  have hEpow := Real.rpow_nonneg (zero_le_one.trans hE) B
  have hEpow' := Real.rpow_nonneg (zero_le_one.trans hE) B'
  have hW := oneHighVariationWeight_nonneg p base high x v
  have hB' := hB.trans hBB'
  calc
    B * H ^ (3 / 4 : ℝ) * E ^ B * oneHighVariationWeight p base high x v ≤
        B' * H ^ (3 / 4 : ℝ) * E ^ B * oneHighVariationWeight p base high x v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBB' hHpow) hEpow) hW
    _ ≤ B' * H ^ (3 / 4 : ℝ) * E ^ B' * oneHighVariationWeight p base high x v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hE hBB') (mul_nonneg hB' hHpow)) hW
    _ ≤ B' * H ^ (3 / 4 : ℝ) * E ^ B' * oneHighVariationWeight p base high' x v :=
      mul_le_mul_of_nonneg_left
        (oneHighVariationWeight_mono hp le_rfl hhigh x v)
        (mul_nonneg (mul_nonneg hB' hHpow) hEpow')

/-- The two radial cases share the same domain and base. Their losses and
constants are enlarged only after the finite parameter prefix is chosen.
Each returned tower is selected before the order j in that prefix. -/
theorem combine_mixed_positive_prefix_bounds
    {I : Type*} {U : Set X} (P : I → PolarPoint → Prop)
    (family : I → ℕ → ℕ → PolarPoint → X → ℝ)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    (base loss : ℕ) (center : X)
    (δ : I → ℕ → PolarPoint → ℝ) (hδ0 : ∀ i q, δ i 0 q = 1)
    (H E : I → ℝ) (hH : ∀ i, 0 ≤ H i) (hE : ∀ i, 1 ≤ E i)
    (hzero : ∀ K : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i b q, b ≤ s → P i q →
      ∃ J : SmoothDirections U (family i 0 b q),
        ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
          |J.D j x v| ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
            oneHighVariationWeight p base (s + loss + d) (x - center) v)
    (hpositive : ∀ K : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i a b q, 0 < a → a + b ≤ s → P i q →
      ∃ J : SmoothDirections U (family i a b q),
        ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
          δ i a q * |J.D j x v| ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
            oneHighVariationWeight p base (s + loss + d) (x - center) v) :
    ∀ K : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i a b q, a + b ≤ s → P i q →
      ∃ J : SmoothDirections U (family i a b q),
        ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
          δ i a q * |J.D j x v| ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
            oneHighVariationWeight p base (s + loss + d) (x - center) v := by
  intro K
  obtain ⟨d0, hd0⟩ := hzero K
  obtain ⟨d1, hd1⟩ := hpositive K
  refine ⟨max d0 d1, fun s => ?_⟩
  obtain ⟨B0, hB0, hb0⟩ := hd0 s
  obtain ⟨B1, hB1, hb1⟩ := hd1 s
  refine ⟨max B0 B1, hB0.trans_le (le_max_left _ _), ?_⟩
  intro i a b q hab hq
  by_cases ha : a = 0
  · subst a
    obtain ⟨J, hJ⟩ := hb0 i b q (by simpa only [zero_add] using hab) hq
    refine ⟨J, fun j hj hjpos x hx v => ?_⟩
    rw [hδ0, one_mul]
    exact (hJ j hj hjpos x hx v).trans
      (flowPrefix_weight_mono p hp (Nat.add_le_add_left (le_max_left d0 d1) (s + loss))
        hB0.le (le_max_left B0 B1) (hH i) (hE i) (x - center) v)
  · obtain ⟨J, hJ⟩ := hb1 i a b q (Nat.pos_of_ne_zero ha) hab hq
    refine ⟨J, fun j hj hjpos x hx v => ?_⟩
    exact (hJ j hj hjpos x hx v).trans
      (flowPrefix_weight_mono p hp (Nat.add_le_add_left (le_max_right d0 d1) (s + loss))
        hB1.le (le_max_right B0 B1) (hH i) (hE i) (x - center) v)

end ContinuousFlexibility.Analysis
