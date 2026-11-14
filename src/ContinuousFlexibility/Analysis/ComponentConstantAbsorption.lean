module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Countable absorption of already established component constants

An unbounded scalar envelope can absorb an arbitrary countable table of
finite constants by choosing its sampling index diagonally. At component m
the selected envelope dominates the first m+1 orders. At each fixed order,
only finitely many earlier components remain, and their constants enter
the single positive multiplier/exponent.

This lemma does not produce a common state neighborhood, a fixed derivative
loss, endpoint estimates, or any geometric compatibility. It does not
modify canonical data or any physical component.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped BigOperators

/-- A single component index absorbs all orders of an arbitrary table of
constants. The multiplier/exponent may depend on the order, not the component. -/
theorem exists_component_constant_absorption
    {E : ℕ → ℝ} (hE : ¬ BddAbove (range E)) (A : ℕ → ℕ → ℝ) :
    ∃ κ : ℕ → ℕ, (∀ m, 1 ≤ E (κ m)) ∧
      ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ m, A s m ≤ B * E (κ m) ^ B := by
  classical
  have hLarge (R : ℝ) : ∃ n, R ≤ E n := by
    by_contra hR
    apply hE
    refine ⟨R, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (lt_of_not_ge (fun hn => hR ⟨n, hn⟩)).le
  have hSelect (m : ℕ) :
      ∃ n, 1 + ∑ j ∈ Finset.range (m + 1), |A j m| ≤ E n :=
    hLarge _
  choose κ hκ using hSelect
  have hOne (m : ℕ) : 1 ≤ E (κ m) :=
    (le_add_of_nonneg_right
      (Finset.sum_nonneg (fun j _ => abs_nonneg (A j m)))).trans (hκ m)
  refine ⟨κ, hOne, ?_⟩
  intro s
  let B : ℝ := 1 + ∑ m ∈ Finset.range s, |A s m|
  have hBOne : 1 ≤ B := by
    dsimp only [B]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => abs_nonneg (A s m)))
  have hB : 0 < B := zero_lt_one.trans_le hBOne
  refine ⟨B, hB, ?_⟩
  intro m
  have hPow : E (κ m) ≤ E (κ m) ^ B := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (hOne m) hBOne
  have hPowOne : 1 ≤ E (κ m) ^ B := (hOne m).trans hPow
  have hBWeight : B ≤ B * E (κ m) ^ B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hPowOne hB.le
  have hEWeight : E (κ m) ≤ B * E (κ m) ^ B := by
    apply hPow.trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hBOne
      (Real.rpow_nonneg (zero_le_one.trans (hOne m)) B)
  by_cases hm : m < s
  · have hSingle : |A s m| ≤ ∑ j ∈ Finset.range s, |A s j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (A s j)) (Finset.mem_range.mpr hm)
    have hAB : A s m ≤ B := by
      have hAbs := le_abs_self (A s m)
      dsimp only [B]
      linarith
    exact hAB.trans hBWeight
  · have hsm : s ≤ m := Nat.le_of_not_gt hm
    calc
      A s m ≤ |A s m| := le_abs_self _
      _ ≤ ∑ j ∈ Finset.range (m + 1), |A j m| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (A j m))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hsm))
      _ ≤ 1 + ∑ j ∈ Finset.range (m + 1), |A j m| := le_add_of_nonneg_left zero_le_one
      _ ≤ E (κ m) := hκ m
      _ ≤ B * E (κ m) ^ B := hEWeight

/-- A genuine divergent envelope supplies the unboundedness hypothesis.
The filter may be the cofinite filter used for material samples. -/
theorem exists_component_constant_absorption_of_tendsto
    {E : ℕ → ℝ} {l : Filter ℕ} [NeBot l]
    (hE : Tendsto E l atTop) (A : ℕ → ℕ → ℝ) :
    ∃ κ : ℕ → ℕ, (∀ m, 1 ≤ E (κ m)) ∧
      ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ m, A s m ≤ B * E (κ m) ^ B := by
  apply exists_component_constant_absorption ?_ A
  rintro ⟨B, hB⟩
  obtain ⟨m, hm⟩ := (hE.eventually_gt_atTop B).exists
  exact (not_le_of_gt hm) (hB (mem_range_self m))

end ContinuousFlexibility.Analysis
