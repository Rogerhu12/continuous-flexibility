module

public import ContinuousFlexibility.Analysis.N07aWeakNormalBootstrap
public import Mathlib.Algebra.BigOperators.Ring.List

/-!
# The finite expansion of the normal recurrence

The recurrence has the five lower solution derivatives (1,1), (0,2),
(1,0), (0,1), (0,0), together with the original source. This explicit
finite list depends only on the two derivative orders. Every leaf is
an angular derivative of the solution or its first normal derivative,
or a derivative of the original source. Its total derivative budget
includes every coefficient factor; source leaves cost two extra orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

def n07aNormalShift (i : Fin 5) : ℕ × ℕ :=
  ![(1, 1), (0, 2), (1, 0), (0, 1), (0, 0)] i

theorem n07aNormalShift_radial_le (i : Fin 5) : (n07aNormalShift i).1 ≤ 1 := by
  fin_cases i <;> decide

theorem n07aNormalShift_order_le (i : Fin 5) :
    (n07aNormalShift i).1 + (n07aNormalShift i).2 ≤ 2 := by
  fin_cases i <;> decide

structure N07aNormalAtom where
  coefficient : Fin 6
  radial : ℕ
  angular : ℕ

structure N07aNormalTerm where
  scalar : ℝ
  atoms : List N07aNormalAtom
  source : Bool
  radial : ℕ
  angular : ℕ

def N07aNormalTerm.order (t : N07aNormalTerm) : ℕ :=
  (t.atoms.map (fun j => j.radial + j.angular)).sum +
    t.radial + t.angular + if t.source then 2 else 0

def N07aNormalTerm.Safe (s : ℕ) (t : N07aNormalTerm) : Prop :=
  (t.source = false → t.radial ≤ 1) ∧ t.order ≤ s

def n07aNormalLeaf (source : Bool) (a b : ℕ) : N07aNormalTerm :=
  ⟨1, [], source, a, b⟩

def n07aNormalPrefix (c : ℝ) (j : N07aNormalAtom) (t : N07aNormalTerm) :
    N07aNormalTerm :=
  ⟨c * t.scalar, j :: t.atoms, t.source, t.radial, t.angular⟩

def n07aNormalBinomial (a b p q : ℕ) : ℝ := (a.choose p : ℝ) * (b.choose q : ℝ)

/-- Full finite expansion of the second-normal recurrence. The last
coefficient, indexed by 5, multiplies the original source. -/
def n07aNormalExpansion : ℕ → ℕ → List N07aNormalTerm
  | 0, b => [n07aNormalLeaf false 0 b]
  | 1, b => [n07aNormalLeaf false 1 b]
  | a + 2, b =>
    ((List.range (b + 1)).flatMap fun q =>
      (List.range (a + 1)).flatMap fun p =>
        (List.finRange 5).flatMap fun i =>
          (n07aNormalExpansion (a - p + (n07aNormalShift i).1)
            (b - q + (n07aNormalShift i).2)).map
              (n07aNormalPrefix (n07aNormalBinomial a b p q)
                ⟨i.castSucc, p, q⟩)) ++
    ((List.range (b + 1)).flatMap fun q =>
      (List.range (a + 1)).map fun p =>
        n07aNormalPrefix (n07aNormalBinomial a b p q) ⟨5, p, q⟩
          (n07aNormalLeaf true (a - p) (b - q)))
termination_by a _ => a
decreasing_by
  have hi := n07aNormalShift_radial_le i
  omega

theorem n07aNormalPrefix_order (c : ℝ) (j : N07aNormalAtom) (t : N07aNormalTerm) :
    (n07aNormalPrefix c j t).order = j.radial + j.angular + t.order := by
  simp only [n07aNormalPrefix, N07aNormalTerm.order, List.map_cons, List.sum_cons]
  omega

/-- The recurrence terminates before using a second normal solution
derivative, while preserving the full one-high-factor order budget. -/
theorem n07aNormalExpansion_safe (a b : ℕ) (t : N07aNormalTerm)
    (ht : t ∈ n07aNormalExpansion a b) : t.Safe (a + b) := by
  induction a using Nat.strong_induction_on generalizing b t with
  | h a ih =>
    cases a with
    | zero =>
      simp only [n07aNormalExpansion, List.mem_singleton] at ht
      subst t
      simp [N07aNormalTerm.Safe, N07aNormalTerm.order, n07aNormalLeaf]
    | succ a =>
      cases a with
      | zero =>
        have he : t = n07aNormalLeaf false 1 b := by
          simpa only [Nat.zero_add, n07aNormalExpansion.eq_2, List.mem_singleton] using ht
        subst t
        simp [N07aNormalTerm.Safe, N07aNormalTerm.order, n07aNormalLeaf]
      | succ a =>
        rw [n07aNormalExpansion, List.mem_append] at ht
        rcases ht with ht | ht
        · obtain ⟨q, hq, hqmem⟩ := List.mem_flatMap.mp ht
          obtain ⟨p, hp, hpmem⟩ := List.mem_flatMap.mp hqmem
          obtain ⟨i, _, himem⟩ := List.mem_flatMap.mp hpmem
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp himem
          have hir := n07aNormalShift_radial_le i
          have hio := n07aNormalShift_order_le i
          have hrec := ih (a - p + (n07aNormalShift i).1) (by omega)
            (b - q + (n07aNormalShift i).2) v hv
          have hp' : p ≤ a := Nat.le_of_lt_succ (List.mem_range.mp hp)
          have hq' : q ≤ b := Nat.le_of_lt_succ (List.mem_range.mp hq)
          refine ⟨hrec.1, ?_⟩
          rw [n07aNormalPrefix_order]
          have ho := hrec.2
          dsimp only at ⊢
          omega
        · obtain ⟨q, hq, hqmem⟩ := List.mem_flatMap.mp ht
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hqmem
          have hp' : p ≤ a := Nat.le_of_lt_succ (List.mem_range.mp hp)
          have hq' : q ≤ b := Nat.le_of_lt_succ (List.mem_range.mp hq)
          constructor
          · simp only [n07aNormalPrefix, n07aNormalLeaf, Bool.true_eq_false, false_implies]
          · rw [n07aNormalPrefix_order]
            simp only [N07aNormalTerm.order, n07aNormalLeaf, List.map_nil,
              List.sum_nil, zero_add, ite_true]
            omega

def N07aNormalAtom.value (A : Fin 6 → PolarPoint → ℝ) (j : N07aNormalAtom)
    (p : PolarPoint) : ℝ := mixedDerivative j.radial j.angular (A j.coefficient) p

def N07aNormalTerm.value (A : Fin 6 → PolarPoint → ℝ) (u f : PolarPoint → ℝ)
    (t : N07aNormalTerm) (p : PolarPoint) : ℝ :=
  t.scalar * (t.atoms.map (fun j => j.value A p)).prod *
    mixedDerivative t.radial t.angular (if t.source then f else u) p

theorem n07aNormalPrefix_value (A : Fin 6 → PolarPoint → ℝ) (u f : PolarPoint → ℝ)
    (c : ℝ) (j : N07aNormalAtom) (t : N07aNormalTerm) (p : PolarPoint) :
    (n07aNormalPrefix c j t).value A u f p = c * j.value A p * t.value A u f p := by
  simp only [n07aNormalPrefix, N07aNormalTerm.value, List.map_cons, List.prod_cons]
  ring

end ContinuousFlexibility.Analysis
