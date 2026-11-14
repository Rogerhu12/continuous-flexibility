module

public import ContinuousFlexibility.Analysis.N07aNormalExpansionData

/-!
# Intrinsic coefficient derivatives in the normal expansion

The coefficients of the first solution derivatives contain one derivative
of a principal coefficient. Charging that derivative is necessary before
interpolating products of the raw geometric jets. The other coefficients
contain no derivative of a raw coefficient. The complete budget still
does not exceed the output order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

def n07aNormalIntrinsicCost (i : Fin 6) : ℕ := ![0, 0, 1, 1, 0, 0] i

theorem n07aNormalIntrinsicCost_shift (i : Fin 5) :
    n07aNormalIntrinsicCost i.castSucc + (n07aNormalShift i).1 +
      (n07aNormalShift i).2 ≤ 2 := by
  fin_cases i <;> decide

def N07aNormalAtom.rawOrder (j : N07aNormalAtom) : ℕ :=
  j.radial + j.angular + n07aNormalIntrinsicCost j.coefficient

def N07aNormalTerm.rawOrder (t : N07aNormalTerm) : ℕ :=
  (t.atoms.map N07aNormalAtom.rawOrder).sum +
    t.radial + t.angular + if t.source then 2 else 0

theorem n07aNormalPrefix_rawOrder (c : ℝ) (j : N07aNormalAtom)
    (t : N07aNormalTerm) :
    (n07aNormalPrefix c j t).rawOrder = j.rawOrder + t.rawOrder := by
  cases hs : t.source <;>
    simp [n07aNormalPrefix, N07aNormalTerm.rawOrder, hs, Nat.add_assoc]

/-- First derivatives already present in the coefficients use the order
saved by their first-order solution factors. They do not add a loss once
per recurrence step. -/
theorem n07aNormalExpansion_rawOrder_le (a b : ℕ) (t : N07aNormalTerm)
    (ht : t ∈ n07aNormalExpansion a b) : t.rawOrder ≤ a + b := by
  induction a using Nat.strong_induction_on generalizing b t with
  | h a ih =>
    cases a with
    | zero =>
      simp only [n07aNormalExpansion, List.mem_singleton] at ht
      subst t
      simp [N07aNormalTerm.rawOrder, n07aNormalLeaf]
    | succ a =>
      cases a with
      | zero =>
        have he : t = n07aNormalLeaf false 1 b := by
          simpa only [Nat.zero_add, n07aNormalExpansion.eq_2, List.mem_singleton] using ht
        subst t
        simp [N07aNormalTerm.rawOrder, n07aNormalLeaf]
      | succ a =>
        rw [n07aNormalExpansion, List.mem_append] at ht
        rcases ht with ht | ht
        · obtain ⟨q, hq, hqmem⟩ := List.mem_flatMap.mp ht
          obtain ⟨p, hp, hpmem⟩ := List.mem_flatMap.mp hqmem
          obtain ⟨i, _, himem⟩ := List.mem_flatMap.mp hpmem
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp himem
          have hir := n07aNormalShift_radial_le i
          have hio := n07aNormalIntrinsicCost_shift i
          have hrec := ih (a - p + (n07aNormalShift i).1) (by omega)
            (b - q + (n07aNormalShift i).2) v hv
          have hp' : p ≤ a := Nat.le_of_lt_succ (List.mem_range.mp hp)
          have hq' : q ≤ b := Nat.le_of_lt_succ (List.mem_range.mp hq)
          rw [n07aNormalPrefix_rawOrder]
          change p + q + n07aNormalIntrinsicCost i.castSucc + v.rawOrder ≤ _
          omega
        · obtain ⟨q, hq, hqmem⟩ := List.mem_flatMap.mp ht
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hqmem
          have hp' : p ≤ a := Nat.le_of_lt_succ (List.mem_range.mp hp)
          have hq' : q ≤ b := Nat.le_of_lt_succ (List.mem_range.mp hq)
          rw [n07aNormalPrefix_rawOrder]
          have hcost : n07aNormalIntrinsicCost 5 = 0 := rfl
          simp only [N07aNormalTerm.rawOrder, N07aNormalAtom.rawOrder,
            n07aNormalLeaf, List.map_nil, List.sum_nil, zero_add, ite_true, hcost]
          omega

end ContinuousFlexibility.Analysis
