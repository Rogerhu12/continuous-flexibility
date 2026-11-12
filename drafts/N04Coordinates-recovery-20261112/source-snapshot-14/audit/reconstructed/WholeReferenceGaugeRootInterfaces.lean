import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasInterfaces
import ContinuousFlexibility.Analysis.WholeComponentFieldSelection
import ContinuousFlexibility.Analysis.PositiveComponentAdjacency

/-!
# The actual two kinds of adjacent pieces at a profile root

A middle cut has strictly negative profile derivative. At a root, two
negative pieces cannot meet because the genuine closed negative
components are disjoint. Two positive components cannot meet either:
their certified opposite negative neighbors would share that root.
Thus the only possibilities are a right negative half followed by a
whole positive component, or a whole positive component followed by a
left negative half. The final adapter uses the unchanged physical
metadata of the fixed-reference-gauge atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04PositiveComponents_no_adjacent_endpoints
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hD : RadialProfileGeometry D) (hN : N01Properties D T S C base loss ε)
    (i j : N04PositiveComponent D.a D.b (deriv D.w)) :
    n04PositiveRight i ≠ n04PositiveLeft j := by
  intro hadj
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hi := n04PositiveComponent_bounds hf i
  have hj := n04PositiveComponent_bounds hf j
  have hiB : n04PositiveEndpoint i true ≠ D.b := by
    change n04PositiveRight i ≠ D.b
    intro he
    linarith [hj.2.1, hj.2.2]
  have hjA : n04PositiveEndpoint j false ≠ D.a := by
    change n04PositiveLeft j ≠ D.a
    intro he
    linarith [hi.1, hi.2.1]
  obtain ⟨m, hm⟩ := n04PositiveEndpoint_exists_negative_neighbor hD hC i true hiB
  obtain ⟨n, hn⟩ := n04PositiveEndpoint_exists_negative_neighbor hD hC j false hjA
  change n04PositiveRight i = C.left m at hm
  change n04PositiveLeft j = C.right n at hn
  have he : C.left m = C.right n := hm.symm.trans (hadj.trans hn)
  have hmClosed : C.left m ∈ Icc (C.left m) (C.right m) :=
    ⟨le_rfl, (hC.1 m).2.1.le⟩
  have hnClosed : C.left m ∈ Icc (C.left n) (C.right n) := by
    rw [he]
    exact ⟨(hC.1 n).2.1.le, le_rfl⟩
  have hmn : m = n := n04_negativeClosed_index_unique hN hmClosed hnClosed
  subst n
  exact (hC.1 m).2.1.ne he

theorem n04WholePiece_adjacent_root_types
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hD : RadialProfileGeometry D) (hN : N01Properties D T S C base loss ε)
    {cut : ℕ → ℝ} (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
    {i j : N04WholePieceIndex D}
    (hadj : n04WholePieceRight C cut i = n04WholePieceLeft C cut j)
    (hzero : deriv D.w (n04WholePieceRight C cut i) = 0) :
    (∃ m p, i = .inl (m, true) ∧ j = .inr p ∧ n04PositiveLeft p = C.right m) ∨
      (∃ p m, i = .inr p ∧ j = .inl (m, false) ∧ n04PositiveRight p = C.left m) := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hnegative (m : ℕ) : deriv D.w (cut m) < 0 :=
    hC.2.2.2.1 m (cut m) (hcut m)
  cases i with
  | inl q =>
      rcases q with ⟨m, side⟩
      cases side with
      | false =>
          change deriv D.w (cut m) = 0 at hzero
          exact ((hnegative m).ne hzero).elim
      | true =>
          change C.right m = n04WholePieceLeft C cut j at hadj
          change deriv D.w (C.right m) = 0 at hzero
          cases j with
          | inl q =>
              rcases q with ⟨n, side⟩
              cases side with
              | false =>
                  change C.right m = C.left n at hadj
                  have hm : C.right m ∈ Icc (C.left m) (C.right m) :=
                    ⟨(hC.1 m).2.1.le, le_rfl⟩
                  have hn : C.right m ∈ Icc (C.left n) (C.right n) := by
                    rw [hadj]
                    exact ⟨le_rfl, (hC.1 n).2.1.le⟩
                  have hmn : m = n := n04_negativeClosed_index_unique hN hm hn
                  subst n
                  exact ((hC.1 m).2.1.ne hadj.symm).elim
              | true =>
                  change C.right m = cut n at hadj
                  have hz : deriv D.w (cut n) = 0 := by
                    rw [← hadj]
                    exact hzero
                  exact ((hnegative n).ne hz).elim
          | inr p =>
              change C.right m = n04PositiveLeft p at hadj
              exact Or.inl ⟨m, p, rfl, rfl, hadj.symm⟩
  | inr p =>
      change n04PositiveRight p = n04WholePieceLeft C cut j at hadj
      change deriv D.w (n04PositiveRight p) = 0 at hzero
      cases j with
      | inl q =>
          rcases q with ⟨m, side⟩
          cases side with
          | false =>
              change n04PositiveRight p = C.left m at hadj
              exact Or.inr ⟨p, m, rfl, rfl, hadj⟩
          | true =>
              change n04PositiveRight p = cut m at hadj
              have hz : deriv D.w (cut m) = 0 := by
                rw [← hadj]
                exact hzero
              exact ((hnegative m).ne hz).elim
      | inr q =>
          exact (n04PositiveComponents_no_adjacent_endpoints hD hN p q hadj).elim

/-- Classification for the same actual reference-gauged record. No raw
first-jet matching hypothesis is used to identify the two pieces. -/
theorem n04WholeReferenceGaugeAtlasData_actual_root_types
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) :
    let W := n04WholeReferenceGaugeAtlasData C L
      (n04bActualTypedAtlas hT hS hN hfield e₀) e cell ψ χ h₀ τ σ Q N
    ∀ i j, W.physicalRight i = W.physicalLeft j →
      deriv D.w (W.physicalRight i) = 0 →
      (∃ m p, e i = .inl (m, true) ∧ e j = .inr p ∧ n04PositiveLeft p = C.right m) ∨
        (∃ p m, e i = .inr p ∧ e j = .inl (m, false) ∧ n04PositiveRight p = C.left m) := by
  dsimp only
  intro i j hadj hzero
  have hi := n04WholeCanonicalAtlasData_actual_reference_radii
    hT hS hN hfield e₀ e cell σ τ Q N i
  have hj := n04WholeCanonicalAtlasData_actual_reference_radii
    hT hS hN hfield e₀ e cell σ τ Q N j
  have hpair : n04WholePieceRight C (n04bActualReferenceCut hN) (e i) =
      n04WholePieceLeft C (n04bActualReferenceCut hN) (e j) :=
    hi.2.symm.trans (hadj.trans hj.1)
  have hz : deriv D.w (n04WholePieceRight C (n04bActualReferenceCut hN) (e i)) = 0 := by
    rw [← hi.2]
    exact hzero
  exact n04WholePiece_adjacent_root_types (n04b_profileGeometry_of_through03 hN)
    hN.1.1 (n04bActualReferenceCut_mem hN) hpair hz

end ContinuousFlexibility.Analysis
