import ContinuousFlexibility.Analysis.N04bReferenceHalves
import ContinuousFlexibility.Analysis.PositiveComponentEndpoints

/-!
# A reference partition by whole positive components

The negative component enumeration and its one genuine cut are retained.
Each positive connected component contributes exactly one interval. The
only omitted radii are actual critical points and negative cuts; no
positive subdivision grid or artificial endpoint is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

abbrev N04WholePieceIndex (D : ReferenceData) :=
  (ℕ × Bool) ⊕ N04PositiveComponent D.a D.b (deriv D.w)

def n04WholePieceLeft {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (cut : ℕ → ℝ) : N04WholePieceIndex D → ℝ
  | .inl i => n04bNegativeLeft C cut i
  | .inr i => n04PositiveLeft i

def n04WholePieceRight {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (cut : ℕ → ℝ) : N04WholePieceIndex D → ℝ
  | .inl i => n04bNegativeRight C cut i
  | .inr i => n04PositiveRight i

def n04WholePiecePositive {D : ReferenceData} : N04WholePieceIndex D → Bool
  | .inl _ => false
  | .inr _ => true

def n04WholePieceExceptional (D : ReferenceData) (cut : ℕ → ℝ) : Set ℝ :=
  {r ∈ radialCore D | deriv D.w r = 0} ∪ Set.range cut

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {cut : ℕ → ℝ}

theorem n04WholePiece_bounds (hf : Continuous (deriv D.w))
    (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) (i : N04WholePieceIndex D) :
    D.a ≤ n04WholePieceLeft C cut i ∧
      n04WholePieceLeft C cut i < n04WholePieceRight C cut i ∧
      n04WholePieceRight C cut i ≤ D.b := by
  cases i with
  | inl i =>
      have h := n04b_negativeHalf_bounds hC hcut i
      exact ⟨h.1.le, h.2.1, h.2.2.le⟩
  | inr i => exact n04PositiveComponent_bounds hf i

theorem n04WholePiece_interval_subset (hf : Continuous (deriv D.w))
    (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) (i : N04WholePieceIndex D) :
    Ioo (n04WholePieceLeft C cut i) (n04WholePieceRight C cut i) ⊆ Ioo D.a D.b := by
  have h := n04WholePiece_bounds hf hC hcut i
  exact fun _ hr => ⟨h.1.trans_lt hr.1, hr.2.trans_le h.2.2⟩

theorem n04WholePiece_positive (hf : Continuous (deriv D.w))
    (i : N04WholePieceIndex D) (hi : n04WholePiecePositive i = true) {r : ℝ}
    (hr : r ∈ Ioo (n04WholePieceLeft C cut i) (n04WholePieceRight C cut i)) :
    0 < deriv D.w r := by
  cases i with
  | inl i => cases hi
  | inr i => exact n04PositiveComponent_interval_pos hf i hr

theorem n04WholePiece_negative (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
    (i : N04WholePieceIndex D) (hi : n04WholePiecePositive i = false) {r : ℝ}
    (hr : r ∈ Ioo (n04WholePieceLeft C cut i) (n04WholePieceRight C cut i)) :
    deriv D.w r < 0 := by
  cases i with
  | inl i => exact n04b_negativeHalf_negative hC hcut i hr
  | inr i => cases hi

theorem n04WholePiece_index_unique (hf : Continuous (deriv D.w))
    (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
    {i j : N04WholePieceIndex D} {r : ℝ}
    (hi : r ∈ Ioo (n04WholePieceLeft C cut i) (n04WholePieceRight C cut i))
    (hj : r ∈ Ioo (n04WholePieceLeft C cut j) (n04WholePieceRight C cut j)) : i = j := by
  cases i with
  | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (n04b_negativeHalf_index_unique hC hcut hi hj)
      | inr j =>
          exact (not_lt_of_ge (n04PositiveComponent_interval_pos hf j hj).le
            (n04b_negativeHalf_negative hC hcut i hi)).elim
  | inr i =>
      cases j with
      | inl j =>
          exact (not_lt_of_ge (n04PositiveComponent_interval_pos hf i hi).le
            (n04b_negativeHalf_negative hC hcut j hj)).elim
      | inr j =>
          have hij : i = j := by
            by_contra hne
            exact Set.disjoint_left.mp
              (n04PositiveComponent_interval_pairwiseDisjoint hf hne) hi hj
          exact congrArg Sum.inr hij

theorem n04WholePieceExceptional_countable (hD : RadialProfileGeometry D) :
    (n04WholePieceExceptional D cut).Countable :=
  (n04_reference_critical_set_countable hD).union (Set.countable_range cut)

theorem n04WholePiece_cover (hf : Continuous (deriv D.w))
    (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) {r : ℝ}
    (hr : r ∈ radialCore D \ n04WholePieceExceptional D cut) :
    ∃! i : N04WholePieceIndex D,
      r ∈ Ioo (n04WholePieceLeft C cut i) (n04WholePieceRight C cut i) := by
  have hne : deriv D.w r ≠ 0 := fun hz => hr.2 (Or.inl ⟨hr.1, hz⟩)
  have hex : ∃ i : N04WholePieceIndex D,
      r ∈ Ioo (n04WholePieceLeft C cut i) (n04WholePieceRight C cut i) := by
    rcases lt_or_gt_of_ne hne with hn | hp
    · obtain ⟨m, hm⟩ := hC.2.2.2.2.1 r hr.1 hn
      have hnotcut : r ≠ cut m := fun he => hr.2 (Or.inr ⟨m, he.symm⟩)
      obtain ⟨j, hj, _⟩ := n04b_negativeHalf_existsUnique hC hcut hm hnotcut
      exact ⟨.inl j, hj⟩
    · obtain ⟨j, hj, _⟩ :=
        (n04PositiveComponent_existsUnique_interval_iff hf r).mpr ⟨hr.1, hp⟩
      exact ⟨.inr j, hj⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun j hj => n04WholePiece_index_unique hf hC hcut hj hi⟩

theorem n04WholePiece_exists_enumeration (hf : Continuous (deriv D.w)) :
    Nonempty (ℕ ≃ N04WholePieceIndex D) := by
  classical
  letI : Countable (N04PositiveComponent D.a D.b (deriv D.w)) :=
    n04PositiveComponent_countable hf
  exact nonempty_equiv_of_countable

def n04WholeCutPair (e : ℕ ≃ N04WholePieceIndex D) (m : ℕ) : ℕ × ℕ :=
  (e.symm (.inl (m, false)), e.symm (.inl (m, true)))

theorem n04WholeCutPair_index (e : ℕ ≃ N04WholePieceIndex D) (m : ℕ) (side : Bool) :
    e (if side then (n04WholeCutPair e m).2 else (n04WholeCutPair e m).1) = .inl (m, side) := by
  cases side <;> simp only [n04WholeCutPair, Bool.false_eq_true, ite_false, ite_true,
    Equiv.apply_symm_apply]

end ContinuousFlexibility.Analysis
