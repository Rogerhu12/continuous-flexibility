import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData
import ContinuousFlexibility.Analysis.N04bActualTypedAtlas

/-!
# The actual moving partition with whole positive components

The negative domains are the same genuine travel halves. Each original
positive subdivision is contained in its full positive component. The
old planar null set therefore still gives coverage; actual negative-half
uniqueness, component disjointness and the two signs give uniqueness.
No radial graph is assigned to a moving cut.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (F G : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeCanonicalAtlasData_actual_domain
    (z : AnnularState S × ℝ) (m : ℕ) :
    physicalPieceOpen S
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) z m =
      match e m with
      | .inl j => n04bTypedPhysicalDomain (D := D) C (n04bActualTravelChart S C L z) (.inl j)
      | .inr i => Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ univ := by
  cases hi : e m with
  | inl j =>
      have h := (n04WholeCanonicalAtlasData_negative_fields C L
        (n04bActualTypedAtlas hT hS hN hfield e₀) e cell F G Q N z m j hi).2.2.2.2.1
      rcases j with ⟨j, side⟩
      cases side <;> simpa only [n04bActualTypedAtlas,
        n04bTypedAtlasData_cutPair, n04bTypedAtlasData_physicalPieceOpen,
        Bool.false_eq_true, ite_false, ite_true, Equiv.apply_symm_apply] using h
  | inr i =>
      exact (n04WholeCanonicalAtlasData_positive_fields C L
        (n04bActualTypedAtlas hT hS hN hfield e₀) e cell F G Q N z m i hi).2.2.2.2.1

theorem n04WholeCanonicalAtlasData_actual_domain_index_unique
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {m n : ℕ} {p : PolarPoint}
    (hm : p ∈ physicalPieceOpen S
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) z m)
    (hn : p ∈ physicalPieceOpen S
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) z n) : m = n := by
  have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hf : Continuous (deriv D.w) :=
    (n04b_profileGeometry_of_through03 hN).2.2.1.1.continuous_deriv (by simp)
  have hΓ (j : ℕ) : MapsTo (n04bActualTravelChart S C L z j)
      (Ioo (C.left j) (C.right j) ×ˢ (univ : Set ℝ))
      (Ioo 0 (C.travel j) ×ˢ (univ : Set ℝ)) :=
    (n04b_actualTravelChart_bijOn hN hS hT hfield hz hs j).mapsTo
  rw [n04WholeCanonicalAtlasData_actual_domain hT hS hN hfield e₀ e cell F G Q N] at hm hn
  apply e.injective
  cases him : e m with
  | inl i =>
      cases hin : e n with
      | inl j =>
          simp only [him, hin] at hm hn
          have hij : i = j := Sum.inl.inj
            (n04b_typed_domain_index_unique hf hC hΓ hm hn)
          exact congrArg Sum.inl hij
      | inr j =>
          simp only [him, hin] at hm hn
          exact (lt_asymm
            (n04b_typed_domain_negative hC (.inl i) rfl hm)
            (n04PositiveComponent_interval_pos hf j hn.1)).elim
  | inr i =>
      cases hin : e n with
      | inl j =>
          simp only [him, hin] at hm hn
          exact (lt_asymm
            (n04PositiveComponent_interval_pos hf i hm.1)
            (n04b_typed_domain_negative hC (.inl j) rfl hn)).elim
      | inr j =>
          simp only [him, hin] at hm hn
          have hij : i = j := by
            by_contra hne
            exact Set.disjoint_left.mp
              (n04PositiveComponent_interval_pairwiseDisjoint hf hne) hm.1 hn.1
          exact congrArg Sum.inr hij

theorem n04WholeCanonicalAtlasData_actual_partition
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    let W := n04WholeCanonicalAtlasData C L
      (n04bActualTypedAtlas hT hS hN hfield e₀) e cell F G Q N
    ∃ E : Set PolarPoint, volume E = 0 ∧
      ∀ p ∈ annularOpen D \ E, ∃! m, p ∈ physicalPieceOpen S W z m := by
  have hf : Continuous (deriv D.w) :=
    (n04b_profileGeometry_of_through03 hN).2.2.1.1.continuous_deriv (by simp)
  obtain ⟨E, hE, hcover⟩ := n04b_actual_typed_domain_partition hT hS hN hfield hz hs
  refine ⟨E, hE, ?_⟩
  intro p hp
  obtain ⟨i, hi, _⟩ := hcover p hp
  have hex : ∃ m, p ∈ physicalPieceOpen S
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) z m := by
    cases i with
    | inl j =>
        refine ⟨e.symm (.inl j), ?_⟩
        rw [n04WholeCanonicalAtlasData_actual_domain hT hS hN hfield e₀ e cell F G Q N,
          Equiv.apply_symm_apply]
        exact hi
    | inr j =>
        refine ⟨e.symm (.inr j.1), ?_⟩
        rw [n04WholeCanonicalAtlasData_actual_domain hT hS hN hfield e₀ e cell F G Q N,
          Equiv.apply_symm_apply]
        exact ⟨n04_positive_piece_mem_component hf j hi.1, mem_univ _⟩
  obtain ⟨m, hm⟩ := hex
  exact ⟨m, hm, fun n hn => n04WholeCanonicalAtlasData_actual_domain_index_unique
    hT hS hN hfield e₀ e cell F G Q N hz hs hn hm⟩

end ContinuousFlexibility.Analysis
