import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData
import ContinuousFlexibility.Analysis.ActualNegativePrincipalDensity

/-!
# Negative principal density on the actual whole atlas

Every stored negative half is contained in its genuine full negative
component. The actual root-coordinate density computation therefore
applies to its stored chart and height, using the old enumeration only
to identify the same constructed functions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04WholeCanonicalAtlasData_actual_negativePrincipalDensity
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
    (N : Set ℝ)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hm : (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell F G Q N).positive m = false)
    (x : PolarPoint) (hx : x ∈ physicalPieceOpen S
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) z m) :
    let W := n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell F G Q N
    (coordinatePrincipalDensity (L.coefficients z) (W.chart z m) (W.height z m)).a x = 1 ∧
      (coordinatePrincipalDensity (L.coefficients z) (W.chart z m) (W.height z m)).b x = 0 ∧
      (coordinatePrincipalDensity (L.coefficients z) (W.chart z m) (W.height z m)).c x =
        -(W.chart z m x).1 := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  cases hi : e m with
  | inl j =>
      let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
      have hk : e₀ k = .inl j := by
        rcases j with ⟨j, side⟩
        cases side <;> simp only [k, K, n04bActualTypedAtlas,
          n04bTypedAtlasData_cutPair, Bool.false_eq_true, ite_false, ite_true,
          Equiv.apply_symm_apply]
      rcases n04WholeCanonicalAtlasData_negative_fields
        C L K e cell F G Q N z m j hi with
        ⟨hl, hr, hpl, hpr, hd, hc, hpos, hF, hG, hh, hco, hV⟩
      have hxold : x ∈ physicalPieceOpen S K z k := by
        rw [← hd]
        exact hx
      have hxraw : x ∈ n04bTypedPhysicalDomain (D := D) C
          (n04bActualTravelChart S C L z) (.inl j) := by
        simpa only [K, n04bActualTypedAtlas,
          n04bTypedAtlasData_physicalPieceOpen, hk] using hxold
      have hxfull := n04b_typed_negative_domain_subset j hxraw
      have h := n04Coordinates_actualAtlas_negativePrincipalDensity
        hT hS hN hfield e₀ hz hs k j.1 j.2 hk hxfull
      have hchart :
          (n04WholeCanonicalAtlasData C L K e cell F G Q N).chart z m =
            K.chart z k := hF
      have hheight :
          (n04WholeCanonicalAtlasData C L K e cell F G Q N).height z m =
            K.height z k := hh
      change (coordinatePrincipalDensity (L.coefficients z)
          ((n04WholeCanonicalAtlasData C L K e cell F G Q N).chart z m)
          ((n04WholeCanonicalAtlasData C L K e cell F G Q N).height z m)).a x = 1 ∧
        (coordinatePrincipalDensity (L.coefficients z)
          ((n04WholeCanonicalAtlasData C L K e cell F G Q N).chart z m)
          ((n04WholeCanonicalAtlasData C L K e cell F G Q N).height z m)).b x = 0 ∧
        (coordinatePrincipalDensity (L.coefficients z)
          ((n04WholeCanonicalAtlasData C L K e cell F G Q N).chart z m)
          ((n04WholeCanonicalAtlasData C L K e cell F G Q N).height z m)).c x =
            -((n04WholeCanonicalAtlasData C L K e cell F G Q N).chart z m x).1
      rw [hchart, hheight]
      exact h
  | inr i =>
      simp only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        hi, n04WholePiecePositive, Bool.true_eq_false] at hm

end ContinuousFlexibility.Analysis
