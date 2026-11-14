module

public import ContinuousFlexibility.Analysis.N04ActualAtlasTransmission
public import ContinuousFlexibility.Analysis.ActualNegativePrincipalDensity
public import ContinuousFlexibility.Analysis.N04bGeometricCompletion

/-!
# Part B for the same actual typed charts

The actual typed atlas already stores the inverse-coordinate operator
fields. Its genuine negative root density and cut transmission supply
Part B after replacing only the unused interior divided-difference field.
This preliminary completion does not use a whole-positive atlas, any
endpoint bound, or any positive interpolation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Complete only the divided field; every chart, inverse, height, root,
physical domain and state-dependent function is the original chosen one. -/
theorem n04bActualTypedAtlas_interiorCompletion_partB
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) :
    N04PartB S C L
      (n04bWithInteriorDivision C (n04bActualTypedAtlas hT hS hN hfield e)) base ε := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hA : N04PartA D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hfields (z : AnnularState S × ℝ) (m : ℕ) :
      K.coefficients z m = inverseChartPrincipalCoefficients (L.coefficients z)
        (K.chart z m) (K.inverseChart z m) (K.height z m) ∧
      ∀ p, K.potential z m p = (if K.positive m then -1 else (1 : ℝ)) *
        inverseChartPotential (L.coefficients z)
          (K.chart z m) (K.inverseChart z m) (K.height z m) p :=
    ⟨rfl, fun _ => rfl⟩
  apply n04bWithInteriorDivision_partB_of_parts
  · exact n04bActualTypedAtlas_cutGeometry hT hS hN hfield e
  · intro z hz hs u hu m θ
    exact n04ActualAtlas_transmission hT hS hN hfield e hz hs u hu m θ
  · intro z hz hs m u hu p hp
    have hx : K.inverseChart z m p ∈ physicalPieceOpen S K z m :=
      (hA.charts z hz hs m).2.1 hp
    obtain ⟨ha, hb, hc⟩ := n04b_field_contDiffAt_on_piece hA hfield hz hs m hx
    have hop := n04b_canonicalOperator_explicit_fields hA hz hs m hp ha hb hc u hu
    have hf := hfields z m
    rw [← hf.1, ← hf.2 p] at hop
    exact hop
  · intro z hz hs k hk p hp
    have hx : K.inverseChart z k p ∈ physicalPieceOpen S K z k :=
      (hA.charts z hz hs k).2.1 hp
    have hFx : K.chart z k (K.inverseChart z k p) = p :=
      (hA.charts z hz hs k).2.2.2.1 p hp
    cases hi : e k with
    | inl j =>
        have hxraw : K.inverseChart z k p ∈
            n04bTypedPhysicalDomain (D := D) C (n04bActualTravelChart S C L z) (.inl j) := by
          simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_physicalPieceOpen, hi]
            using hx
        have hxfull := n04b_typed_negative_domain_subset j hxraw
        have hd := n04Coordinates_actualAtlas_negativePrincipalDensity
          hT hS hN hfield e hz hs k j.1 j.2 hi hxfull
        change
          (coordinatePrincipalDensity (L.coefficients z) (K.chart z k) (K.height z k)).a
              (K.inverseChart z k p) = 1 ∧
            (coordinatePrincipalDensity (L.coefficients z) (K.chart z k) (K.height z k)).b
              (K.inverseChart z k p) = 0 ∧
            (coordinatePrincipalDensity (L.coefficients z) (K.chart z k) (K.height z k)).c
              (K.inverseChart z k p) = -(K.chart z k (K.inverseChart z k p)).1 at hd
        rw [hFx] at hd
        rw [(hfields z k).1]
        exact hd
    | inr i =>
        have htrue : K.positive k = true := by
          simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_positive, hi,
            n04TypedPiecePositive]
        rw [htrue] at hk
        cases hk

end ContinuousFlexibility.Analysis
