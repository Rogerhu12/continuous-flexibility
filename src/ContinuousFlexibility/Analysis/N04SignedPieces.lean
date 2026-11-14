module

public import ContinuousFlexibility.Analysis.N04CriticalSet
public import ContinuousFlexibility.Analysis.N04PieceData
public import ContinuousFlexibility.Analysis.N04PositiveComponents
public import ContinuousFlexibility.Analysis.N04NegativeHalves
public import ContinuousFlexibility.Analysis.N04IntervalSubdivision
public import Mathlib.Basic.Denumerable

/-!
# The actual signed physical partition

Negative components keep their two midpoint halves. Positive components
are subdivided into closed interior intervals. Their only omissions are
the simple critical radii and the countable subdivision grids. An
equivalence, rather than a surjective enumeration, transfers this
partition to the natural-number indices of CanonicalData.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

abbrev N04PositivePieceIndex (D : ReferenceData) :=
  N04PositiveComponent D.a D.b (deriv D.w) × (Bool × ℕ)

abbrev N04PieceIndex (D : ReferenceData) := (ℕ × Bool) ⊕ N04PositivePieceIndex D

def n04TypedPieceLeft {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) : N04PieceIndex D → ℝ
  | .inl i => n04NegativeLeft C i
  | .inr i => n04SubdivisionLeft (n04PositiveLeft i.1) (n04PositiveRight i.1) i.2

def n04TypedPieceRight {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) : N04PieceIndex D → ℝ
  | .inl i => n04NegativeRight C i
  | .inr i => n04SubdivisionRight (n04PositiveLeft i.1) (n04PositiveRight i.1) i.2

def n04TypedPiecePositive {D : ReferenceData} : N04PieceIndex D → Bool
  | .inl _ => false
  | .inr _ => true

def n04TypedPieceReversed {D : ReferenceData} : N04PieceIndex D → Bool
  | .inl i => i.2
  | .inr _ => false

/-- A cell is selected by actual membership of the physical midpoint. -/
def n04CellAt (D : ReferenceData) (r : ℝ) : ℕ := by
  classical
  exact if h : ∃ m, r ∈ D.cells m then h.choose else 0

theorem n04_cell_at_mem {D : ReferenceData} (hD : RadialPartition D)
    {r : ℝ} (hr : r ∈ radialCore D) : r ∈ D.cells (n04CellAt D r) := by
  have hex : ∃ m, r ∈ D.cells m := by
    by_contra h
    have hz (m : ℕ) : D.localizer m r = 0 := by
      by_contra hm
      exact h ⟨m, hD.2.2.1 m (by simpa only [Function.mem_support] using hm)⟩
    have hsum := (hD.2.2.2.2.1 r hr).2
    simp only [hz, tsum_zero] at hsum
    exact zero_ne_one hsum
  simp only [n04CellAt, dif_pos hex]
  exact hex.choose_spec

def n04PieceExceptional (D : ReferenceData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) : Set ℝ :=
  {r ∈ radialCore D | deriv D.w r = 0} ∪
    (Set.range (n04NegativeMid C) ∪
      ⋃ i : N04PositiveComponent D.a D.b (deriv D.w),
        n04SubdivisionExceptional (n04PositiveLeft i) (n04PositiveRight i))

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}

theorem n04_typed_piece_bounds (hf : Continuous (deriv D.w))
    (hC : controlGeometryConditions D S C) (i : N04PieceIndex D) :
    D.a < n04TypedPieceLeft C i ∧
      n04TypedPieceLeft C i < n04TypedPieceRight C i ∧
      n04TypedPieceRight C i < D.b := by
  cases i with
  | inl i => exact n04NegativeHalf_bounds hC i
  | inr i =>
    have hc := n04PositiveComponent_bounds hf i.1
    have hs := n04_subdivision_bounds hc.2.1 i.2
    exact ⟨hc.1.trans_lt hs.1, hs.2.1, hs.2.2.trans_le hc.2.2⟩

theorem n04_positive_piece_mem_component (hf : Continuous (deriv D.w))
    (i : N04PositivePieceIndex D) {r : ℝ}
    (hr : r ∈ Ioo (n04SubdivisionLeft (n04PositiveLeft i.1) (n04PositiveRight i.1) i.2)
      (n04SubdivisionRight (n04PositiveLeft i.1) (n04PositiveRight i.1) i.2)) :
    r ∈ Ioo (n04PositiveLeft i.1) (n04PositiveRight i.1) :=
  n04_subdivision_closed_subset (n04PositiveComponent_bounds hf i.1).2.1 i.2
    ⟨hr.1.le, hr.2.le⟩

theorem n04_typed_piece_positive (hf : Continuous (deriv D.w))
    (i : N04PieceIndex D) (hi : n04TypedPiecePositive i = true) {r : ℝ}
    (hr : r ∈ Ioo (n04TypedPieceLeft C i) (n04TypedPieceRight C i)) :
    0 < deriv D.w r := by
  cases i with
  | inl i => simp [n04TypedPiecePositive] at hi
  | inr i =>
    exact n04PositiveComponent_interval_pos hf i.1
      (n04_positive_piece_mem_component hf i hr)

theorem n04_typed_piece_negative (hC : controlGeometryConditions D S C)
    (i : N04PieceIndex D) (hi : n04TypedPiecePositive i = false) {r : ℝ}
    (hr : r ∈ Ioo (n04TypedPieceLeft C i) (n04TypedPieceRight C i)) :
    deriv D.w r < 0 := by
  cases i with
  | inl i => exact n04NegativeHalf_interval_negative hC i hr
  | inr i => simp [n04TypedPiecePositive] at hi

theorem n04_typed_piece_index_unique (hf : Continuous (deriv D.w))
    (hC : controlGeometryConditions D S C) {i j : N04PieceIndex D} {r : ℝ}
    (hi : r ∈ Ioo (n04TypedPieceLeft C i) (n04TypedPieceRight C i))
    (hj : r ∈ Ioo (n04TypedPieceLeft C j) (n04TypedPieceRight C j)) : i = j := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (n04NegativeHalf_index_unique hC hi hj)
    | inr j =>
      have hn := n04NegativeHalf_interval_negative hC i hi
      have hp := n04PositiveComponent_interval_pos hf j.1
        (n04_positive_piece_mem_component hf j hj)
      exact (not_lt_of_ge hp.le hn).elim
  | inr i =>
    cases j with
    | inl j =>
      have hn := n04NegativeHalf_interval_negative hC j hj
      have hp := n04PositiveComponent_interval_pos hf i.1
        (n04_positive_piece_mem_component hf i hi)
      exact (not_lt_of_ge hp.le hn).elim
    | inr j =>
      rcases i with ⟨ci, si⟩
      rcases j with ⟨cj, sj⟩
      have hci := n04_positive_piece_mem_component hf (ci, si) hi
      have hcj := n04_positive_piece_mem_component hf (cj, sj) hj
      have hc : ci = cj := by
        by_contra hne
        exact (Set.disjoint_left.mp
          (n04PositiveComponent_interval_pairwiseDisjoint hf hne)) hci hcj
      subst cj
      have hs : si = sj := n04_subdivision_index_unique
        (n04PositiveComponent_bounds hf ci).2.1 hi hj
      subst sj
      rfl

theorem n04_piece_exceptional_countable (hD : RadialProfileGeometry D) :
    (n04PieceExceptional D C).Countable := by
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  letI : Countable (N04PositiveComponent D.a D.b (deriv D.w)) :=
    n04PositiveComponent_countable hf
  exact (n04_reference_critical_set_countable hD).union
    ((Set.countable_range _).union
      (Set.countable_iUnion fun i => n04_subdivision_exceptional_countable
        (n04PositiveLeft i) (n04PositiveRight i)))

theorem n04_typed_piece_cover (hf : Continuous (deriv D.w))
    (hC : controlGeometryConditions D S C) {r : ℝ}
    (hr : r ∈ radialCore D \ n04PieceExceptional D C) :
    ∃! i : N04PieceIndex D,
      r ∈ Ioo (n04TypedPieceLeft C i) (n04TypedPieceRight C i) := by
  have hne : deriv D.w r ≠ 0 := fun hz => hr.2 (Or.inl ⟨hr.1, hz⟩)
  have hex : ∃ i : N04PieceIndex D,
      r ∈ Ioo (n04TypedPieceLeft C i) (n04TypedPieceRight C i) := by
    rcases lt_or_gt_of_ne hne with hn | hp
    · have hmid : r ∉ Set.range (n04NegativeMid C) :=
        fun hm => hr.2 (Or.inr (Or.inl hm))
      obtain ⟨i, hi, _⟩ := n04NegativeHalf_existsUnique hC hr.1 hn hmid
      exact ⟨.inl i, hi⟩
    · obtain ⟨i, hi, _⟩ :=
        (n04PositiveComponent_existsUnique_interval_iff hf r).mpr ⟨hr.1, hp⟩
      have hgrid : r ∉ n04SubdivisionExceptional (n04PositiveLeft i) (n04PositiveRight i) :=
        fun hg => hr.2 (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨i, hg⟩)))
      obtain ⟨j, hj, _⟩ := n04_subdivision_cover
        (n04PositiveComponent_bounds hf i).2.1 hi hgrid
      exact ⟨.inr (i, j), hj⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun j hj => n04_typed_piece_index_unique hf hC hj hi⟩

/-- An injective enumeration of the genuine signed pieces, retaining the
same negative components and their actual midpoint cuts. -/
theorem n04_exists_signed_pieces (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C) :
    ∃ P : N04PieceData, N04PieceGeometry D P ∧ N04NegativeCutPairs C P := by
  classical
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  letI : Countable (N04PositiveComponent D.a D.b (deriv D.w)) :=
    n04PositiveComponent_countable hf
  obtain ⟨e⟩ : Nonempty (ℕ ≃ N04PieceIndex D) := nonempty_equiv_of_countable
  let P : N04PieceData := {
    left := fun m => n04TypedPieceLeft C (e m)
    right := fun m => n04TypedPieceRight C (e m)
    cell := fun m => n04CellAt D
      ((n04TypedPieceLeft C (e m) + n04TypedPieceRight C (e m)) / 2)
    positive := fun m => n04TypedPiecePositive (e m)
    reversed := fun m => n04TypedPieceReversed (e m)
    cutPair := fun m => (e.symm (.inl (m, false)), e.symm (.inl (m, true))) }
  refine ⟨P, ?_, ?_⟩
  · refine ⟨fun m => n04_typed_piece_bounds hf hC (e m), ?_, ?_,
      n04PieceExceptional D C, n04_piece_exceptional_countable hD, ?_⟩
    · intro m hm r hr
      exact n04_typed_piece_positive hf (e m) hm hr
    · intro m hm r hr
      exact n04_typed_piece_negative hC (e m) hm hr
    · intro r hr
      obtain ⟨i, hi, hu⟩ := n04_typed_piece_cover hf hC hr
      refine ⟨e.symm i, ?_, ?_⟩
      · simpa only [P, Equiv.apply_symm_apply] using hi
      · intro m hm
        apply e.injective
        simpa only [Equiv.apply_symm_apply] using hu (e m) hm
  · intro m
    simp only [P, Equiv.apply_symm_apply, n04TypedPiecePositive,
      n04TypedPieceReversed, n04TypedPieceLeft, n04TypedPieceRight,
      n04NegativeLeft, n04NegativeRight, n04NegativeMid, Bool.false_eq_true,
      if_false, if_true, and_self]

end ContinuousFlexibility.Analysis
