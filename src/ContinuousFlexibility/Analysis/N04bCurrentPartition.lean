module

public import ContinuousFlexibility.Analysis.N04SignedPieces
public import ContinuousFlexibility.Analysis.N04bCutCurve
public import ContinuousFlexibility.Analysis.N04bAtlasBoundary

/-!
# The actual planar partition by moving characteristic halves

Use the existing signed index type. Its positive intervals remain fixed;
each negative component is split by its actual travel chart. Only the
countable reference radial exception and the genuine smooth middle cuts
are omitted. This proves the current planar partition without a radial
graph assumption on any cut.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData}

def n04bTypedPhysicalDomain (C : NonlinearGeometryData S)
    (Γ : ℕ → PolarPoint → PolarPoint) : N04PieceIndex D → Set PolarPoint
  | .inl i => n04bTravelHalfDomain
      (Ioo (C.left i.1) (C.right i.1) ×ˢ univ) (Γ i.1) (C.travel i.1) i.2
  | .inr i => Ioo
      (n04SubdivisionLeft (n04PositiveLeft i.1) (n04PositiveRight i.1) i.2)
      (n04SubdivisionRight (n04PositiveLeft i.1) (n04PositiveRight i.1) i.2) ×ˢ univ

variable {C : NonlinearGeometryData S} {Γ : ℕ → PolarPoint → PolarPoint}

theorem n04b_typed_negative_domain_subset
    (i : ℕ × Bool) :
    n04bTypedPhysicalDomain (D := D) C Γ (.inl i) ⊆
      Ioo (C.left i.1) (C.right i.1) ×ˢ (univ : Set ℝ) := by
  intro p hp
  exact (mem_n04bTravelDomain.mp hp).1

theorem n04b_typed_domain_positive
    (hf : Continuous (deriv D.w)) (i : N04PieceIndex D)
    (hi : n04TypedPiecePositive i = true) {p : PolarPoint}
    (hp : p ∈ n04bTypedPhysicalDomain C Γ i) : 0 < deriv D.w p.1 := by
  cases i with
  | inl i => simp only [n04TypedPiecePositive, Bool.false_eq_true] at hi
  | inr i =>
    exact n04PositiveComponent_interval_pos hf i.1
      (n04_positive_piece_mem_component hf i hp.1)

theorem n04b_typed_domain_negative
    (hC : controlGeometryConditions D S C) (i : N04PieceIndex D)
    (hi : n04TypedPiecePositive i = false) {p : PolarPoint}
    (hp : p ∈ n04bTypedPhysicalDomain C Γ i) : deriv D.w p.1 < 0 := by
  cases i with
  | inl i => exact hC.2.2.2.1 i.1 p.1 (n04b_typed_negative_domain_subset i hp).1
  | inr i => simp only [n04TypedPiecePositive, Bool.true_eq_false] at hi

theorem n04b_typed_domain_index_unique
    (hf : Continuous (deriv D.w)) (hC : controlGeometryConditions D S C)
    (hΓ : ∀ m, MapsTo (Γ m) (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (Ioo 0 (C.travel m) ×ˢ (univ : Set ℝ)))
    {i j : N04PieceIndex D} {p : PolarPoint}
    (hi : p ∈ n04bTypedPhysicalDomain C Γ i)
    (hj : p ∈ n04bTypedPhysicalDomain C Γ j) : i = j := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      obtain ⟨m, side⟩ := i
      obtain ⟨n, other⟩ := j
      have hmn : m = n := by
        by_contra hne
        exact Set.disjoint_left.mp (hC.2.2.1 m n hne)
          (n04b_typed_negative_domain_subset (m, side) hi).1
          (n04b_typed_negative_domain_subset (n, other) hj).1
      subst n
      cases side <;> cases other
      · rfl
      · exact (Set.disjoint_left.mp (n04b_travelHalves_split (hΓ m)).1 hi hj).elim
      · exact (Set.disjoint_left.mp (n04b_travelHalves_split (hΓ m)).1 hj hi).elim
      · rfl
    | inr j =>
      have hn := n04b_typed_domain_negative hC (.inl i) rfl hi
      have hp := n04b_typed_domain_positive hf (.inr j) rfl hj
      exact (lt_asymm hn hp).elim
  | inr i =>
    cases j with
    | inl j =>
      have hp := n04b_typed_domain_positive hf (.inr i) rfl hi
      have hn := n04b_typed_domain_negative hC (.inl j) rfl hj
      exact (lt_asymm hn hp).elim
    | inr j =>
      exact n04_typed_piece_index_unique hf hC
        (i := .inr i) (j := .inr j) hi.1 hj.1

theorem n04b_typed_domain_cover
    (hf : Continuous (deriv D.w)) (hC : controlGeometryConditions D S C)
    (hΓ : ∀ m, MapsTo (Γ m) (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (Ioo 0 (C.travel m) ×ˢ (univ : Set ℝ)))
    {p : PolarPoint} (hp : p ∈ annularOpen D)
    (href : p.1 ∉ n04PieceExceptional D C)
    (hcut : ∀ m, p ∉ n04bTravelCut
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) (Γ m) (C.travel m / 2)) :
    ∃! i : N04PieceIndex D, p ∈ n04bTypedPhysicalDomain C Γ i := by
  obtain ⟨i, hi, _⟩ := n04_typed_piece_cover hf hC ⟨hp.1, href⟩
  have hex : ∃ i : N04PieceIndex D, p ∈ n04bTypedPhysicalDomain C Γ i := by
    cases i with
    | inl i =>
      have hm : p ∈ Ioo (C.left i.1) (C.right i.1) ×ˢ (univ : Set ℝ) :=
        ⟨n04NegativeHalf_piece_subset_original hC i hi, mem_univ _⟩
      have hs : p ∈ n04bTravelHalfDomain
          (Ioo (C.left i.1) (C.right i.1) ×ˢ (univ : Set ℝ))
          (Γ i.1) (C.travel i.1) false ∪
          n04bTravelHalfDomain
          (Ioo (C.left i.1) (C.right i.1) ×ˢ (univ : Set ℝ))
          (Γ i.1) (C.travel i.1) true := by
        rw [(n04b_travelHalves_split (hΓ i.1)).2]
        exact ⟨hm, hcut i.1⟩
      rcases hs with hl | hr
      · exact ⟨.inl (i.1, false), hl⟩
      · exact ⟨.inl (i.1, true), hr⟩
    | inr i => exact ⟨.inr i, hi, mem_univ _⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun j hj => n04b_typed_domain_index_unique hf hC hΓ hj hi⟩

/-- Countably many actual smooth travel cuts give exactly the planar
null-set contract needed by the current-domain atlas. -/
theorem n04b_current_planar_partition
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    {G : ℕ → PolarPoint → PolarPoint}
    (hT : ∀ m, 0 < C.travel m)
    (hΓ : ∀ m, BijOn (Γ m) (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (Ioo 0 (C.travel m) ×ˢ (univ : Set ℝ)))
    (hG : ∀ m, MapsTo (G m) (Ioo 0 (C.travel m) ×ˢ (univ : Set ℝ))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hΓG : ∀ m q, q ∈ Ioo 0 (C.travel m) ×ˢ (univ : Set ℝ) → Γ m (G m q) = q)
    (hGsmooth : ∀ m, ContDiffOn ℝ ∞ (G m) (Ioo 0 (C.travel m) ×ˢ (univ : Set ℝ))) :
    ∃ E : Set PolarPoint, volume E = 0 ∧
      ∀ p ∈ annularOpen D \ E, ∃! i : N04PieceIndex D,
        p ∈ n04bTypedPhysicalDomain C Γ i := by
  let cuts : Set PolarPoint := ⋃ m, n04bTravelCut
    (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) (Γ m) (C.travel m / 2)
  let E : Set PolarPoint := (n04PieceExceptional D C ×ˢ univ) ∪ cuts
  have hcuts : volume cuts = 0 := by
    apply measure_iUnion_null
    intro m
    exact n04b_volume_travelCut (hΓ m) (hG m) (hΓG m) (hGsmooth m)
      ⟨half_pos (hT m), half_lt_self (hT m)⟩
  have href : volume (n04PieceExceptional D C ×ˢ (univ : Set ℝ)) = 0 :=
    n04b_volume_radial_cylinder_eq_zero
      ((n04_piece_exceptional_countable hD).measure_zero volume)
  refine ⟨E, measure_union_null href hcuts, ?_⟩
  intro p hp
  apply n04b_typed_domain_cover (hD.2.2.1.1.continuous_deriv (by simp)) hC
    (fun m => (hΓ m).mapsTo) hp.1
  · intro hr
    exact hp.2 (Or.inl ⟨hr, mem_univ _⟩)
  · intro m hm
    exact hp.2 (Or.inr (Set.mem_iUnion.mpr ⟨m, hm⟩))

end ContinuousFlexibility.Analysis
