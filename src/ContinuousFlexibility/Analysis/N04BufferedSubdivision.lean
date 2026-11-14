module

public import ContinuousFlexibility.Analysis.N04IntervalSubdivision

/-!
# A positive subdivision with a prescribed central interval

The central piece can contain the compact normalization support with a
strict buffer at both ends. The remaining pieces are the existing dyadic
subdivisions of the two gaps. Every closed piece stays inside the original
open interval, including when that interval touches the ambient boundary.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

abbrev N04BufferedIndex : Type := Option (Bool × (Bool × ℕ))

def n04BufferedLeft (a c d b : ℝ) : N04BufferedIndex → ℝ
  | none => c
  | some (side, i) => if side then n04SubdivisionLeft d b i else n04SubdivisionLeft a c i

def n04BufferedRight (a c d b : ℝ) : N04BufferedIndex → ℝ
  | none => d
  | some (side, i) => if side then n04SubdivisionRight d b i else n04SubdivisionRight a c i

def n04BufferedExceptional (a c d b : ℝ) : Set ℝ :=
  ({c} ∪ {d}) ∪ n04SubdivisionExceptional a c ∪ n04SubdivisionExceptional d b

theorem n04_buffered_bounds {a c d b : ℝ}
    (hac : a < c) (hcd : c < d) (hdb : d < b) (i : N04BufferedIndex) :
    a < n04BufferedLeft a c d b i ∧
      n04BufferedLeft a c d b i < n04BufferedRight a c d b i ∧
      n04BufferedRight a c d b i < b := by
  cases i with
  | none => exact ⟨hac, hcd, hdb⟩
  | some i =>
    rcases i with ⟨side, i⟩
    cases side
    · have h := n04_subdivision_bounds hac i
      exact ⟨h.1, h.2.1, h.2.2.trans (hcd.trans hdb)⟩
    · have h := n04_subdivision_bounds hdb i
      exact ⟨(hac.trans hcd).trans h.1, h.2.1, h.2.2⟩

theorem n04_buffered_closed_subset {a c d b : ℝ}
    (hac : a < c) (hcd : c < d) (hdb : d < b) (i : N04BufferedIndex) :
    Icc (n04BufferedLeft a c d b i) (n04BufferedRight a c d b i) ⊆ Ioo a b := by
  intro r hr
  have h := n04_buffered_bounds hac hcd hdb i
  exact ⟨h.1.trans_le hr.1, hr.2.trans_lt h.2.2⟩

theorem n04_buffered_noncentral_disjoint_middle {a c d b : ℝ}
    (hac : a < c) (hcd : c < d) (hdb : d < b)
    {i : N04BufferedIndex} (hi : i ≠ none) :
    Disjoint (Ioo (n04BufferedLeft a c d b i) (n04BufferedRight a c d b i))
      (Icc c d) := by
  apply Set.disjoint_left.mpr
  intro r hr hm
  cases i with
  | none => exact hi rfl
  | some i =>
    rcases i with ⟨side, i⟩
    cases side
    · have hb := n04_subdivision_bounds hac i
      exact (not_lt_of_ge hm.1) (hr.2.trans hb.2.2)
    · have hb := n04_subdivision_bounds hdb i
      exact (not_lt_of_ge hm.2) (hb.1.trans hr.1)

theorem n04_buffered_index_unique {a c d b r : ℝ}
    (hac : a < c) (hcd : c < d) (hdb : d < b) {i j : N04BufferedIndex}
    (hi : r ∈ Ioo (n04BufferedLeft a c d b i) (n04BufferedRight a c d b i))
    (hj : r ∈ Ioo (n04BufferedLeft a c d b j) (n04BufferedRight a c d b j)) :
    i = j := by
  by_cases hin : i = none
  · subst i
    by_cases hjn : j = none
    · exact hjn.symm
    · exact False.elim ((Set.disjoint_left.mp
        (n04_buffered_noncentral_disjoint_middle hac hcd hdb hjn)) hj ⟨hi.1.le, hi.2.le⟩)
  by_cases hjn : j = none
  · subst j
    exact False.elim ((Set.disjoint_left.mp
      (n04_buffered_noncentral_disjoint_middle hac hcd hdb hin)) hi ⟨hj.1.le, hj.2.le⟩)
  cases i with
  | none => exact (hin rfl).elim
  | some i =>
    cases j with
    | none => exact (hjn rfl).elim
    | some j =>
      rcases i with ⟨si, i⟩
      rcases j with ⟨sj, j⟩
      cases si <;> cases sj
      · exact congrArg (fun k => some (false, k)) (n04_subdivision_index_unique hac hi hj)
      · have hli := n04_subdivision_bounds hac i
        have hrj := n04_subdivision_bounds hdb j
        have hrc : r < c := hi.2.trans hli.2.2
        have hdr : d < r := hrj.1.trans hj.1
        exact False.elim ((not_lt_of_ge (hcd.trans hdr).le) hrc)
      · have hri := n04_subdivision_bounds hdb i
        have hlj := n04_subdivision_bounds hac j
        have hdr : d < r := hri.1.trans hi.1
        have hrc : r < c := hj.2.trans hlj.2.2
        exact False.elim ((not_lt_of_ge (hcd.trans hdr).le) hrc)
      · exact congrArg (fun k => some (true, k)) (n04_subdivision_index_unique hdb hi hj)

theorem n04_buffered_pairwise_disjoint {a c d b : ℝ}
    (hac : a < c) (hcd : c < d) (hdb : d < b) :
    Pairwise (fun i j : N04BufferedIndex =>
      Disjoint (Ioo (n04BufferedLeft a c d b i) (n04BufferedRight a c d b i))
        (Ioo (n04BufferedLeft a c d b j) (n04BufferedRight a c d b j))) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun _ hi hj => hij (n04_buffered_index_unique hac hcd hdb hi hj))

theorem n04_buffered_exceptional_countable (a c d b : ℝ) :
    (n04BufferedExceptional a c d b).Countable :=
  (((Set.countable_singleton c).union (Set.countable_singleton d)).union
    (n04_subdivision_exceptional_countable a c)).union
      (n04_subdivision_exceptional_countable d b)

theorem n04_buffered_cover {a c d b r : ℝ}
    (hac : a < c) (hcd : c < d) (hdb : d < b) (hr : r ∈ Ioo a b)
    (hE : r ∉ n04BufferedExceptional a c d b) :
    ∃! i : N04BufferedIndex,
      r ∈ Ioo (n04BufferedLeft a c d b i) (n04BufferedRight a c d b i) := by
  have hrc : r ≠ c := fun h => hE (Or.inl (Or.inl (Or.inl h)))
  have hrd : r ≠ d := fun h => hE (Or.inl (Or.inl (Or.inr h)))
  have hEl : r ∉ n04SubdivisionExceptional a c := fun h => hE (Or.inl (Or.inr h))
  have hEr : r ∉ n04SubdivisionExceptional d b := fun h => hE (Or.inr h)
  have hex : ∃ i : N04BufferedIndex,
      r ∈ Ioo (n04BufferedLeft a c d b i) (n04BufferedRight a c d b i) := by
    rcases lt_or_gt_of_ne hrc with h | h
    · obtain ⟨i, hi, _⟩ := n04_subdivision_cover hac ⟨hr.1, h⟩ hEl
      exact ⟨some (false, i), hi⟩
    · rcases lt_or_gt_of_ne hrd with h' | h'
      · exact ⟨none, h, h'⟩
      · obtain ⟨i, hi, _⟩ := n04_subdivision_cover hdb ⟨h', hr.2⟩ hEr
        exact ⟨some (true, i), hi⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun j hj => n04_buffered_index_unique hac hcd hdb hj hi⟩

end ContinuousFlexibility.Analysis
