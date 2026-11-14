module

public import ContinuousFlexibility.Statements.Nonlinear

/-!
# The two halves of each negative radial component

The existing control geometry already enumerates all negative components.
Splitting each at its midpoint preserves their original indices and gives
nondegenerate pieces whose closed intervals lie inside the radial core.
Only the countable set of midpoints is omitted from their union.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData}

def n04NegativeMid (C : NonlinearGeometryData S) (m : ℕ) : ℝ :=
  (C.left m + C.right m) / 2

/-- `false` is the left half and `true` is the right half. -/
def n04NegativeLeft (C : NonlinearGeometryData S) (i : ℕ × Bool) : ℝ :=
  if i.2 then n04NegativeMid C i.1 else C.left i.1

def n04NegativeRight (C : NonlinearGeometryData S) (i : ℕ × Bool) : ℝ :=
  if i.2 then C.right i.1 else n04NegativeMid C i.1

@[simp] theorem n04NegativeLeft_false (C : NonlinearGeometryData S) (m : ℕ) :
    n04NegativeLeft C (m, false) = C.left m := by
  simp only [n04NegativeLeft, Bool.false_eq_true, if_false]

@[simp] theorem n04NegativeLeft_true (C : NonlinearGeometryData S) (m : ℕ) :
    n04NegativeLeft C (m, true) = n04NegativeMid C m := by
  simp only [n04NegativeLeft, if_true]

@[simp] theorem n04NegativeRight_false (C : NonlinearGeometryData S) (m : ℕ) :
    n04NegativeRight C (m, false) = n04NegativeMid C m := by
  simp only [n04NegativeRight, Bool.false_eq_true, if_false]

@[simp] theorem n04NegativeRight_true (C : NonlinearGeometryData S) (m : ℕ) :
    n04NegativeRight C (m, true) = C.right m := by
  simp only [n04NegativeRight, if_true]

variable {C : NonlinearGeometryData S}

theorem n04NegativeMid_mem_original (hC : controlGeometryConditions D S C) (m : ℕ) :
    n04NegativeMid C m ∈ Ioo (C.left m) (C.right m) := by
  have hlt := (hC.1 m).2.1
  constructor <;> dsimp only [n04NegativeMid] <;> linarith

theorem n04NegativeHalf_bounds (hC : controlGeometryConditions D S C) (i : ℕ × Bool) :
    D.a < n04NegativeLeft C i ∧ n04NegativeLeft C i < n04NegativeRight C i ∧
      n04NegativeRight C i < D.b := by
  obtain ⟨m, side⟩ := i
  obtain ⟨ha, hlr, hb⟩ := hC.1 m
  have hm := n04NegativeMid_mem_original hC m
  cases side
  · simpa only [n04NegativeLeft_false, n04NegativeRight_false] using
      And.intro ha (And.intro hm.1 (hm.2.trans hb))
  · simpa only [n04NegativeLeft_true, n04NegativeRight_true] using
      And.intro (ha.trans hm.1) (And.intro hm.2 hb)

theorem n04NegativeHalf_piece_subset_original
    (hC : controlGeometryConditions D S C) (i : ℕ × Bool) :
    Ioo (n04NegativeLeft C i) (n04NegativeRight C i) ⊆
      Ioo (C.left i.1) (C.right i.1) := by
  obtain ⟨m, side⟩ := i
  have hm := n04NegativeMid_mem_original hC m
  intro r hr
  cases side
  · have hhalf : r ∈ Ioo (C.left m) (n04NegativeMid C m) := by
      simpa only [n04NegativeLeft_false, n04NegativeRight_false] using hr
    exact ⟨hhalf.1, hhalf.2.trans hm.2⟩
  · have hhalf : r ∈ Ioo (n04NegativeMid C m) (C.right m) := by
      simpa only [n04NegativeLeft_true, n04NegativeRight_true] using hr
    exact ⟨hm.1.trans hhalf.1, hhalf.2⟩

theorem n04NegativeHalf_interval_subset_core
    (hC : controlGeometryConditions D S C) (i : ℕ × Bool) :
    Ioo (n04NegativeLeft C i) (n04NegativeRight C i) ⊆ Ioo D.a D.b := by
  have hb := n04NegativeHalf_bounds hC i
  exact fun r hr => ⟨hb.1.trans hr.1, hr.2.trans hb.2.2⟩

theorem n04NegativeHalf_closed_subset_core
    (hC : controlGeometryConditions D S C) (i : ℕ × Bool) :
    Icc (n04NegativeLeft C i) (n04NegativeRight C i) ⊆ Ioo D.a D.b := by
  have hb := n04NegativeHalf_bounds hC i
  exact fun r hr => ⟨hb.1.trans_le hr.1, hr.2.trans_lt hb.2.2⟩

theorem n04NegativeHalf_interval_negative
    (hC : controlGeometryConditions D S C) (i : ℕ × Bool) {r : ℝ}
    (hr : r ∈ Ioo (n04NegativeLeft C i) (n04NegativeRight C i)) :
    deriv D.w r < 0 :=
  hC.2.2.2.1 i.1 r (n04NegativeHalf_piece_subset_original hC i hr)

/-- Membership identifies both the original component and the side of its cut. -/
theorem n04NegativeHalf_index_unique
    (hC : controlGeometryConditions D S C) {i j : ℕ × Bool} {r : ℝ}
    (hri : r ∈ Ioo (n04NegativeLeft C i) (n04NegativeRight C i))
    (hrj : r ∈ Ioo (n04NegativeLeft C j) (n04NegativeRight C j)) : i = j := by
  obtain ⟨m, side⟩ := i
  obtain ⟨n, other⟩ := j
  have hmn : m = n := by
    by_contra hne
    exact Set.disjoint_left.mp (hC.2.2.1 m n hne)
      (n04NegativeHalf_piece_subset_original hC (m, side) hri)
      (n04NegativeHalf_piece_subset_original hC (n, other) hrj)
  subst n
  cases side <;> cases other
  · rfl
  · have hleft : r < n04NegativeMid C m := by
      simpa only [n04NegativeRight_false] using hri.2
    have hright : n04NegativeMid C m < r := by
      simpa only [n04NegativeLeft_true] using hrj.1
    exact (lt_asymm hleft hright).elim
  · have hright : n04NegativeMid C m < r := by
      simpa only [n04NegativeLeft_true] using hri.1
    have hleft : r < n04NegativeMid C m := by
      simpa only [n04NegativeRight_false] using hrj.2
    exact (lt_asymm hleft hright).elim
  · rfl

theorem n04NegativeHalf_interval_pairwiseDisjoint
    (hC : controlGeometryConditions D S C) :
    Pairwise (fun i j : ℕ × Bool =>
      Disjoint (Ioo (n04NegativeLeft C i) (n04NegativeRight C i))
        (Ioo (n04NegativeLeft C j) (n04NegativeRight C j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro r hri hrj
  exact hij (n04NegativeHalf_index_unique hC hri hrj)

theorem n04NegativeHalf_existsUnique
    (hC : controlGeometryConditions D S C) {r : ℝ}
    (hrCore : r ∈ Ioo D.a D.b) (hneg : deriv D.w r < 0)
    (hnotMid : r ∉ Set.range (n04NegativeMid C)) :
    ∃! i : ℕ × Bool, r ∈ Ioo (n04NegativeLeft C i) (n04NegativeRight C i) := by
  obtain ⟨m, hrm⟩ := hC.2.2.2.2.1 r hrCore hneg
  have hrne : r ≠ n04NegativeMid C m := by
    intro heq
    exact hnotMid ⟨m, heq.symm⟩
  have hex : ∃ i : ℕ × Bool,
      r ∈ Ioo (n04NegativeLeft C i) (n04NegativeRight C i) := by
    rcases lt_or_gt_of_ne hrne with hleft | hright
    · refine ⟨(m, false), ?_⟩
      simpa only [n04NegativeLeft_false, n04NegativeRight_false, Set.mem_Ioo] using
        And.intro hrm.1 hleft
    · refine ⟨(m, true), ?_⟩
      simpa only [n04NegativeLeft_true, n04NegativeRight_true, Set.mem_Ioo] using
        And.intro hright hrm.2
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun j hj => n04NegativeHalf_index_unique hC hj hi⟩

end ContinuousFlexibility.Analysis
