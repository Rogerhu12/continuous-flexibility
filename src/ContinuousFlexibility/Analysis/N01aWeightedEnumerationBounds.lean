import ContinuousFlexibility.Analysis.N01aWeightedEnumeration
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean

/-!
# Linear weights from finite density witnesses

A real depth parameter can be chosen separately for each enumeration
index. Rounding only the resulting weight bound costs one fixed unit.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

variable {α : Type*} [Infinite α] [DecidableEq α]

theorem exists_n01aWeightEnumeration_linear_bound (f : α → ℕ)
    (hf : ∀ N : ℕ, {a | f a ≤ N}.Finite) {d H N₀ : ℝ}
    (hd : 0 < d) (hH : 0 < H)
    (hwitness : ∀ N : ℝ, N₀ ≤ N → ∃ S : Finset α,
      d * N - 1 ≤ (S.card : ℝ) ∧ ∀ a ∈ S, (f a : ℝ) ≤ H * (1 + N)) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      (f (n01aWeightEnumeration f n) : ℝ) ≤ B * (1 + (n : ℝ)) := by
  let C : ℝ := H * (1 + max 0 N₀ + 2 / d) + 1
  let D : ℝ := H / d
  have hC : 0 < C := by dsimp only [C]; positivity
  have hD : 0 < D := div_pos hH hd
  refine ⟨C + D, add_pos hC hD, fun n => ?_⟩
  let N : ℝ := max 0 N₀ + ((n : ℝ) + 2) / d
  have hN : N₀ ≤ N := by
    have hdiv : 0 ≤ ((n : ℝ) + 2) / d := by positivity
    dsimp only [N]
    linarith only [le_max_right (0 : ℝ) N₀, hdiv]
  obtain ⟨S, hcard, hweight⟩ := hwitness N hN
  have hmul : d * N = d * max 0 N₀ + (n : ℝ) + 2 := by
    dsimp only [N]
    field_simp
    ring
  have hncard : n < S.card := by
    have hnonneg : 0 ≤ d * max 0 N₀ := mul_nonneg hd.le (le_max_left _ _)
    have hreal : (n : ℝ) < (S.card : ℝ) := by linarith only [hcard, hmul, hnonneg]
    exact_mod_cast hreal
  have hNnonneg : 0 ≤ N := by dsimp only [N]; positivity
  have harg : 0 ≤ H * (1 + N) := mul_nonneg hH.le (by linarith only [hNnonneg])
  have hbound : f (n01aWeightEnumeration f n) ≤ ⌈H * (1 + N)⌉₊ := by
    apply n01aWeightEnumeration_le_of_finite_family f hf S hncard
    intro a ha
    exact_mod_cast (hweight a ha).trans (Nat.le_ceil (H * (1 + N)))
  have hceil : (⌈H * (1 + N)⌉₊ : ℝ) ≤ H * (1 + N) + 1 :=
    (Nat.ceil_lt_add_one harg).le
  have hform : H * (1 + N) + 1 = C + D * (n : ℝ) := by
    dsimp only [N, C, D]
    ring
  calc
    (f (n01aWeightEnumeration f n) : ℝ) ≤ (⌈H * (1 + N)⌉₊ : ℝ) := by
      exact_mod_cast hbound
    _ ≤ H * (1 + N) + 1 := hceil
    _ = C + D * (n : ℝ) := hform
    _ ≤ (C + D) * (1 + (n : ℝ)) := by
      nlinarith only [hD.le, mul_nonneg hC.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

end ContinuousFlexibility.Statements
