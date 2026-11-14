module

public import ContinuousFlexibility.Analysis.N07aNormalRecurrence
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact evaluation of the finite normal expansion

The finite list fixed by the two derivative orders evaluates to the
actual derivative of the solution of the original second-normal equation.
Together with `n07aNormalExpansion_safe`, this gives a finite expansion
whose unknown leaves have at most one normal derivative and whose full
coefficient/source derivative budget is bounded by the output order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def n07aNormalTermsValue (A : Fin 6 → PolarPoint → ℝ) (u f : PolarPoint → ℝ)
    (L : List N07aNormalTerm) (x : PolarPoint) : ℝ :=
  (L.map (fun t => t.value A u f x)).sum

private theorem n07aNormalTermsValue_append (A : Fin 6 → PolarPoint → ℝ)
    (u f : PolarPoint → ℝ) (L M : List N07aNormalTerm) (x : PolarPoint) :
    n07aNormalTermsValue A u f (L ++ M) x =
      n07aNormalTermsValue A u f L x + n07aNormalTermsValue A u f M x := by
  simp only [n07aNormalTermsValue, List.map_append, List.sum_append]

private theorem n07aNormalTermsValue_flatMap {ι : Type*}
    (A : Fin 6 → PolarPoint → ℝ) (u f : PolarPoint → ℝ)
    (L : List ι) (g : ι → List N07aNormalTerm) (x : PolarPoint) :
    n07aNormalTermsValue A u f (L.flatMap g) x =
      (L.map (fun i => n07aNormalTermsValue A u f (g i) x)).sum := by
  induction L with
  | nil => simp [n07aNormalTermsValue]
  | cons i L ih =>
    simp only [List.flatMap_cons, n07aNormalTermsValue_append, ih,
      List.map_cons, List.sum_cons]

private theorem n07aNormalTermsValue_prefix (A : Fin 6 → PolarPoint → ℝ)
    (u f : PolarPoint → ℝ) (L : List N07aNormalTerm)
    (c : ℝ) (j : N07aNormalAtom) (x : PolarPoint) :
    n07aNormalTermsValue A u f (L.map (n07aNormalPrefix c j)) x =
      c * j.value A x * n07aNormalTermsValue A u f L x := by
  simp only [n07aNormalTermsValue, List.map_map, Function.comp_def,
    n07aNormalPrefix_value]
  exact List.sum_map_mul_left L (fun t => t.value A u f x) (c * j.value A x)

private theorem n07a_sum_map_range (n : ℕ) (g : ℕ → ℝ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem n07aNormalTermsValue_leaf (A : Fin 6 → PolarPoint → ℝ)
    (u f : PolarPoint → ℝ) (source : Bool) (a b : ℕ) (x : PolarPoint) :
    (n07aNormalLeaf source a b).value A u f x =
      mixedDerivative a b (if source then f else u) x := by
  simp [n07aNormalLeaf, N07aNormalTerm.value]

theorem n07aNormalTermsValue_step (A : Fin 6 → PolarPoint → ℝ)
    (u f : PolarPoint → ℝ) (a b : ℕ) (x : PolarPoint) :
    n07aNormalTermsValue A u f (n07aNormalExpansion (a + 2) b) x =
      (∑ q ∈ Finset.range (b + 1), ∑ p ∈ Finset.range (a + 1), ∑ i : Fin 5,
        n07aNormalBinomial a b p q * mixedDerivative p q (A i.castSucc) x *
          n07aNormalTermsValue A u f
            (n07aNormalExpansion (a - p + (n07aNormalShift i).1)
              (b - q + (n07aNormalShift i).2)) x) +
      ∑ q ∈ Finset.range (b + 1), ∑ p ∈ Finset.range (a + 1),
        n07aNormalBinomial a b p q * mixedDerivative p q (A 5) x *
          mixedDerivative (a - p) (b - q) f x := by
  rw [n07aNormalExpansion.eq_3, n07aNormalTermsValue_append]
  apply congrArg₂ (· + ·)
  · simp only [n07aNormalTermsValue_flatMap, n07aNormalTermsValue_prefix,
      n07a_sum_map_range, ← Fin.sum_univ_def, N07aNormalAtom.value]
  · rw [n07aNormalTermsValue_flatMap, n07a_sum_map_range]
    apply Finset.sum_congr rfl
    intro q _
    simp only [n07aNormalTermsValue, List.map_map, Function.comp_def,
      n07aNormalPrefix_value, n07aNormalTermsValue_leaf,
      N07aNormalAtom.value, ite_true, n07a_sum_map_range]

/-- Exact finite normal expansion on the open domain of the genuine
equation. The finite list is independent of the coefficients, solution,
source, and evaluation point. -/
theorem n07a_normalExpansion_exact {U : Set PolarPoint} (hU : IsOpen U)
    {A : Fin 6 → PolarPoint → ℝ} {u f : PolarPoint → ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hu : ContDiffOn ℝ ∞ u U) (hf : ContDiffOn ℝ ∞ f U)
    (heq : EqOn (mixedDerivative 2 0 u) (n07aNormalRhs A u f) U)
    (a b : ℕ) {x : PolarPoint} (hx : x ∈ U) :
    mixedDerivative a b u x =
      n07aNormalTermsValue A u f (n07aNormalExpansion a b) x := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    cases a with
    | zero =>
      simp [n07aNormalExpansion.eq_1, n07aNormalTermsValue, n07aNormalTermsValue_leaf]
    | succ a =>
      cases a with
      | zero =>
        simpa only [Nat.zero_add, n07aNormalExpansion.eq_2, n07aNormalTermsValue,
          List.map_singleton, List.sum_singleton, n07aNormalTermsValue_leaf,
          Bool.false_eq_true, ite_false]
      | succ a =>
        rw [n07a_normal_mixed_recursion hU hA hu hf heq a b hx,
          n07aNormalTermsValue_step]
        apply congrArg₂ (· + ·) _ rfl
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro i _
        have hi := n07aNormalShift_radial_le i
        rw [ih (a - p + (n07aNormalShift i).1) (by omega)
          (b - q + (n07aNormalShift i).2)]

end ContinuousFlexibility.Analysis
