module

public import ContinuousFlexibility.Analysis.WholeCanonicalAtlasReferencePartition

/-!
# Actual interfaces of the whole-component atlas

An adjacent pair can meet only at a true profile root or at the one
retained optical cut inside a negative component. The argument uses the
actual reference radii and the same enumeration as the atlas fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04WholePiece_adjacent_interface
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {cut : ℕ → ℝ}
    (hf : Continuous (deriv D.w)) (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
    {i j : N04WholePieceIndex D}
    (hadj : n04WholePieceRight C cut i = n04WholePieceLeft C cut j) :
    deriv D.w (n04WholePieceRight C cut i) = 0 ∨
      ∃ m, i = .inl (m, false) ∧ j = .inl (m, true) := by
  by_cases hzero : deriv D.w (n04WholePieceRight C cut i) = 0
  · exact Or.inl hzero
  right
  have hleftPiece : ∃ m, i = .inl (m, false) := by
    cases i with
    | inl q =>
        rcases q with ⟨m, side⟩
        cases side with
        | false => exact ⟨m, rfl⟩
        | true =>
            change deriv D.w (C.right m) ≠ 0 at hzero
            exact (hzero (hC.2.1 m).2.1).elim
    | inr i =>
        rcases n04PositiveEndpoint_ambient_or_zero hf i true with hamb | hroot
        · change n04PositiveRight i = D.b at hamb
          change n04PositiveRight i = n04WholePieceLeft C cut j at hadj
          have hj := n04WholePiece_bounds hf hC hcut j
          exfalso
          linarith [hj.2.1, hj.2.2]
        · exact (hzero hroot.2).elim
  obtain ⟨m, rfl⟩ := hleftPiece
  change deriv D.w (cut m) ≠ 0 at hzero
  cases j with
  | inl q =>
      rcases q with ⟨n, side⟩
      cases side with
      | false =>
          change cut m = C.left n at hadj
          have hz : deriv D.w (cut m) = 0 := by
            rw [hadj]
            exact (hC.2.1 n).1
          exact (hzero hz).elim
      | true =>
          change cut m = cut n at hadj
          have hm : m = n := by
            by_contra hne
            apply Set.disjoint_left.mp (hC.2.2.1 m n hne) (hcut m)
            rw [hadj]
            exact hcut n
          subst n
          exact ⟨m, rfl, rfl⟩
  | inr j =>
      change cut m = n04PositiveLeft j at hadj
      rcases n04PositiveEndpoint_ambient_or_zero hf j false with hamb | hroot
      · change n04PositiveLeft j = D.a at hamb
        have hm := (hC.1 m).1.trans (hcut m).1
        exfalso
        linarith
      · have hz : deriv D.w (cut m) = 0 := by
          rw [hadj]
          exact hroot.2
        exact (hzero hz).elim

theorem n04WholeCanonicalAtlasData_actual_interfaceClassification
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
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
    (N : Set ℝ) :
    CanonicalGeometry.PhysicalInterfaceClassification D
      (n04WholeCanonicalAtlasData C L
        (n04bActualTypedAtlas hT hS hN hfield e₀) e cell F G Q N) := by
  intro i j _hij hadj
  have hD := n04b_profileGeometry_of_through03 hN
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hi := n04WholeCanonicalAtlasData_actual_reference_radii
    hT hS hN hfield e₀ e cell F G Q N i
  have hj := n04WholeCanonicalAtlasData_actual_reference_radii
    hT hS hN hfield e₀ e cell F G Q N j
  have hpair : n04WholePieceRight C (n04bActualReferenceCut hN) (e i) =
      n04WholePieceLeft C (n04bActualReferenceCut hN) (e j) :=
    hi.2.symm.trans (hadj.trans hj.1)
  rcases n04WholePiece_adjacent_interface hf hC
      (n04bActualReferenceCut_mem hN) hpair with hz | ⟨m, hm, hn⟩
  · left
    rw [hi.2]
    exact hz
  · right
    refine ⟨m, Prod.ext ?_ ?_⟩
    · change e.symm (.inl (m, false)) = i
      apply e.injective
      simpa only [Equiv.apply_symm_apply] using hm.symm
    · change e.symm (.inl (m, true)) = j
      apply e.injective
      simpa only [Equiv.apply_symm_apply] using hn.symm

end ContinuousFlexibility.Analysis
