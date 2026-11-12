import ContinuousFlexibility.Analysis.ActualNegativeReferenceDerivativeSourceBounds
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData
import ContinuousFlexibility.Analysis.N01ReturnMargins

/-!
# The two derivative source costs on the same whole-component atlas

The retained negative piece uses the original actual chart, inverse and
height. Its current point and its reference preimage belong to the same
negative component by the actual open chart and inverse maps. A genuine
host of that component therefore evaluates the uniform coefficient cost
at the current physical radius. No reference-point agreement or material
bound is supplied as an extra hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- These are the actual `i = 0` and `i = 2` reference source fields of
the same atlas record, with a common bound preceding every valid state,
piece and physical point. The middle `i = 1` field is not covered. -/
theorem n04WholeCanonicalAtlasData_negative_derivativeSource_bound
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
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    ∃ B P : ℝ, 0 < B ∧ 0 ≤ P ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ n m side, e n = .inl (m, side) → ∀ x ∈ physicalPieceOpen S W z n,
        |canonicalPrimitiveField D T C W z n (.inr (.inr (0 : Fin 3))) x| ≤
            B * T.E0 x.1 ^ P ∧
          |canonicalPrimitiveField D T C W z n (.inr (.inr (2 : Fin 3))) x| ≤
            B * T.E0 x.1 ^ P := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
  have hA : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e₀
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    (n04b_reference_valid_of_through03 hN).1
  have hsref : stateSector S C.referenceState :=
    (n04b_reference_valid_of_through03 hN).2
  obtain ⟨B, P, hB, hP, hb⟩ :=
    n04Coordinates_actual_reference_derivativeSource_material_bound hT hS hN hfield e₀
  obtain ⟨_, _, hhosts⟩ := n01Properties_returnMargins hN.1.1
  refine ⟨B, P, hB, hP, ?_⟩
  intro z hz hs n m side hi x hx
  let k := if side then (K.cutPair m).2 else (K.cutPair m).1
  have hk : e₀ k = .inl (m, side) := by
    have hpair : K.cutPair m =
        (e₀.symm (.inl (m, false)), e₀.symm (.inl (m, true))) := rfl
    dsimp only [k]
    rw [hpair]
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      Equiv.apply_symm_apply]
  have hstored (v : AnnularState S × ℝ) :
      physicalPieceOpen S W v n = physicalPieceOpen S K v k ∧
        W.chart v n = K.chart v k ∧ W.inverseChart v n = K.inverseChart v k ∧
        W.height v n = K.height v k := by
    rcases n04WholeCanonicalAtlasData_negative_fields C L K e cell F G Q N v n
      (m, side) hi with ⟨_, _, _, _, hdomain, _, _, hchart, hinverse, hheight, _, _⟩
    exact ⟨hdomain, hchart, hinverse, hheight⟩
  have hsubset (v : AnnularState S × ℝ) :
      physicalPieceOpen S K v k ⊆ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    intro p hp
    apply n04b_typed_negative_domain_subset (D := D) (C := C)
      (Γ := n04bActualTravelChart S C L v) (m, side)
    simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_physicalPieceOpen, hk] using hp
  have hxK : x ∈ physicalPieceOpen S K z k := by rwa [(hstored z).1] at hx
  let y := canonicalReferencePoint C W z n x
  have hyK : y ∈ physicalPieceOpen S K (C.referenceState, 0) k := by
    dsimp only [y, canonicalReferencePoint]
    rw [(hstored (C.referenceState, 0)).2.2.1, (hstored z).2.1]
    exact (hA.charts (C.referenceState, 0) href hsref k).2.1
      ((hA.charts z hz hs k).1 hxK)
  have hxwhole := hsubset z hxK
  have hywhole := hsubset (C.referenceState, 0) hyK
  obtain ⟨j, hhost, _⟩ := (hhosts m).2
  have hbound := hb m j hhost k side hk y hywhole x.1 (hhost hxwhole.1)
  have hsource : canonicalReferenceSourceFactor C W z n x =
      K.height (C.referenceState, 0) k y /
        |planeJacobian (K.chart (C.referenceState, 0) k) y| := by
    change W.height (C.referenceState, 0) n y /
      |planeJacobian (W.chart (C.referenceState, 0) n) y| = _
    rw [(hstored (C.referenceState, 0)).2.2.2, (hstored (C.referenceState, 0)).2.1]
  change |canonicalReferenceSourceFactor C W z n x * deriv D.w y.1| ≤
      B * T.E0 x.1 ^ P ∧
    |canonicalReferenceSourceFactor C W z n x * (deriv D.w y.1 / y.1)| ≤
      B * T.E0 x.1 ^ P
  rw [hsource]
  exact hbound

end ContinuousFlexibility.Analysis
