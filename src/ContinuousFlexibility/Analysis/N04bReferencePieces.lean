module

public import ContinuousFlexibility.Analysis.N04bReferenceHalves

/-!
# Reference piece metadata with arbitrary interior negative cuts

The signed index type and positive subdivisions are unchanged. One fixed
equivalence with ℕ indexes both this reference metadata and the later
moving physical domains. The exceptional set is countable; retaining the
old exceptional radii does not constrain the new interval endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {S : PhysicalSpacesData}

def n04bReferenceTypedLeft (C : NonlinearGeometryData S) (cut : ℕ → ℝ) :
    N04PieceIndex D → ℝ
  | .inl i => n04bNegativeLeft C cut i
  | .inr i => n04TypedPieceLeft C (.inr i)

def n04bReferenceTypedRight (C : NonlinearGeometryData S) (cut : ℕ → ℝ) :
    N04PieceIndex D → ℝ
  | .inl i => n04bNegativeRight C cut i
  | .inr i => n04TypedPieceRight C (.inr i)

def n04bReferenceExceptional (D : ReferenceData)
    (C : NonlinearGeometryData S) (cut : ℕ → ℝ) : Set ℝ :=
  n04PieceExceptional D C ∪ Set.range cut

variable {C : NonlinearGeometryData S} {cut : ℕ → ℝ}

theorem n04b_referenceTyped_bounds
    (hf : Continuous (deriv D.w)) (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) (i : N04PieceIndex D) :
    D.a < n04bReferenceTypedLeft C cut i ∧
      n04bReferenceTypedLeft C cut i < n04bReferenceTypedRight C cut i ∧
      n04bReferenceTypedRight C cut i < D.b := by
  cases i with
  | inl i => exact n04b_negativeHalf_bounds hC hcut i
  | inr i => exact n04_typed_piece_bounds hf hC (.inr i)

theorem n04b_referenceTyped_positive
    (hf : Continuous (deriv D.w)) (i : N04PieceIndex D)
    (hi : n04TypedPiecePositive i = true) {r : ℝ}
    (hr : r ∈ Ioo (n04bReferenceTypedLeft C cut i) (n04bReferenceTypedRight C cut i)) :
    0 < deriv D.w r := by
  cases i with
  | inl i => simp [n04TypedPiecePositive] at hi
  | inr i => exact n04_typed_piece_positive (C := C) hf (.inr i) rfl hr

theorem n04b_referenceTyped_negative
    (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) (i : N04PieceIndex D)
    (hi : n04TypedPiecePositive i = false) {r : ℝ}
    (hr : r ∈ Ioo (n04bReferenceTypedLeft C cut i) (n04bReferenceTypedRight C cut i)) :
    deriv D.w r < 0 := by
  cases i with
  | inl i => exact n04b_negativeHalf_negative hC hcut i hr
  | inr i => simp [n04TypedPiecePositive] at hi

theorem n04b_referenceTyped_index_unique
    (hf : Continuous (deriv D.w)) (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
    {i j : N04PieceIndex D} {r : ℝ}
    (hi : r ∈ Ioo (n04bReferenceTypedLeft C cut i) (n04bReferenceTypedRight C cut i))
    (hj : r ∈ Ioo (n04bReferenceTypedLeft C cut j) (n04bReferenceTypedRight C cut j)) :
    i = j := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (n04b_negativeHalf_index_unique hC hcut hi hj)
    | inr j =>
      exact (not_lt_of_ge
        (n04_typed_piece_positive (C := C) hf (.inr j) rfl hj).le
        (n04b_negativeHalf_negative hC hcut i hi)).elim
  | inr i =>
    cases j with
    | inl j =>
      exact (not_lt_of_ge
        (n04_typed_piece_positive (C := C) hf (.inr i) rfl hi).le
        (n04b_negativeHalf_negative hC hcut j hj)).elim
    | inr j => exact n04_typed_piece_index_unique hf hC hi hj

theorem n04b_referenceExceptional_countable (hD : RadialProfileGeometry D) :
    (n04bReferenceExceptional D C cut).Countable :=
  (n04_piece_exceptional_countable (C := C) hD).union (Set.countable_range cut)

theorem n04b_referenceTyped_cover
    (hf : Continuous (deriv D.w)) (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) {r : ℝ}
    (hr : r ∈ radialCore D \ n04bReferenceExceptional D C cut) :
    ∃! i : N04PieceIndex D,
      r ∈ Ioo (n04bReferenceTypedLeft C cut i) (n04bReferenceTypedRight C cut i) := by
  have hold : r ∈ radialCore D \ n04PieceExceptional D C :=
    ⟨hr.1, fun he => hr.2 (Or.inl he)⟩
  obtain ⟨i, hi, _⟩ := n04_typed_piece_cover hf hC hold
  have hex : ∃ i : N04PieceIndex D,
      r ∈ Ioo (n04bReferenceTypedLeft C cut i) (n04bReferenceTypedRight C cut i) := by
    cases i with
    | inl i =>
      have hne : r ≠ cut i.1 := fun he => hr.2 (Or.inr ⟨i.1, he.symm⟩)
      obtain ⟨j, hj, _⟩ := n04b_negativeHalf_existsUnique hC hcut
        (n04NegativeHalf_piece_subset_original hC i hi) hne
      exact ⟨.inl j, hj⟩
    | inr i => exact ⟨.inr i, hi⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun j hj => n04b_referenceTyped_index_unique hf hC hcut hj hi⟩

/-- Use this same equivalence for the reference and moving domains. -/
def n04bReferencePieces (C : NonlinearGeometryData S) (cut : ℕ → ℝ)
    (e : ℕ ≃ N04PieceIndex D) : N04PieceData where
  left := fun m => n04bReferenceTypedLeft C cut (e m)
  right := fun m => n04bReferenceTypedRight C cut (e m)
  cell := fun m => n04CellAt D
    ((n04bReferenceTypedLeft C cut (e m) + n04bReferenceTypedRight C cut (e m)) / 2)
  positive := fun m => n04TypedPiecePositive (e m)
  reversed := fun m => n04TypedPieceReversed (e m)
  cutPair := fun m => (e.symm (.inl (m, false)), e.symm (.inl (m, true)))

theorem n04bReferencePieces_geometry
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
    (e : ℕ ≃ N04PieceIndex D) :
    N04PieceGeometry D (n04bReferencePieces C cut e) := by
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  refine ⟨fun m => n04b_referenceTyped_bounds hf hC hcut (e m), ?_, ?_,
    n04bReferenceExceptional D C cut, n04b_referenceExceptional_countable hD, ?_⟩
  · intro m hm r hr
    exact n04b_referenceTyped_positive hf (e m) hm hr
  · intro m hm r hr
    exact n04b_referenceTyped_negative hC hcut (e m) hm hr
  · intro r hr
    obtain ⟨i, hi, hu⟩ := n04b_referenceTyped_cover hf hC hcut hr
    refine ⟨e.symm i, ?_, ?_⟩
    · simpa only [n04bReferencePieces, Equiv.apply_symm_apply] using hi
    · intro m hm
      apply e.injective
      simpa only [Equiv.apply_symm_apply] using hu (e m) hm

/-- All negative metadata are computed from the specified cut. This
replaces the old midpoint-specific conclusion without changing it. -/
theorem n04bReferencePieces_cutPair
    (C : NonlinearGeometryData S) (cut : ℕ → ℝ)
    (e : ℕ ≃ N04PieceIndex D) (m : ℕ) :
    let P := n04bReferencePieces C cut e
    P.positive (P.cutPair m).1 = false ∧ P.positive (P.cutPair m).2 = false ∧
      P.reversed (P.cutPair m).1 = false ∧ P.reversed (P.cutPair m).2 = true ∧
      P.left (P.cutPair m).1 = C.left m ∧ P.right (P.cutPair m).2 = C.right m ∧
      P.right (P.cutPair m).1 = cut m ∧ P.left (P.cutPair m).2 = cut m := by
  simp [n04bReferencePieces, n04TypedPiecePositive, n04TypedPieceReversed,
    n04bReferenceTypedLeft, n04bReferenceTypedRight, n04bNegativeLeft, n04bNegativeRight]

theorem n04bReferencePieces_positive_endpoints
    (C : NonlinearGeometryData S) (cut : ℕ → ℝ)
    (e : ℕ ≃ N04PieceIndex D) (i : N04PositivePieceIndex D) :
    (n04bReferencePieces C cut e).left (e.symm (.inr i)) =
        n04TypedPieceLeft C (.inr i) ∧
      (n04bReferencePieces C cut e).right (e.symm (.inr i)) =
        n04TypedPieceRight C (.inr i) := by
  simp [n04bReferencePieces, n04bReferenceTypedLeft, n04bReferenceTypedRight]

theorem n04b_exists_piece_enumeration (hf : Continuous (deriv D.w)) :
    Nonempty (ℕ ≃ N04PieceIndex D) := by
  classical
  letI : Countable (N04PositiveComponent D.a D.b (deriv D.w)) :=
    n04PositiveComponent_countable hf
  exact nonempty_equiv_of_countable

end ContinuousFlexibility.Analysis
