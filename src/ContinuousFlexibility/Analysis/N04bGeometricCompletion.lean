import ContinuousFlexibility.Analysis.N04bFieldRegularity
import ContinuousFlexibility.Analysis.N04bCanonicalOperator
import ContinuousFlexibility.Analysis.N04bPositiveDivision

/-!
# Completing an actual geometric atlas with its operator fields

Once the genuine charts, height, cut traces and root principal-density
calculation have been constructed, the coefficient and potential fields
are determined by the actual coordinate formula. The full operator
identity is proved from raw physical regularity, and the positive
interior divided differences are then defined by their actual quotients.

This is an assembly lemma for the coordinate construction. Its geometric
and principal-density inputs must still be established by that construction;
it does not close the N04b blueprint by itself.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- Raw spatial regularity applies at every actual physical chart point. -/
theorem n04b_field_contDiffAt_on_piece
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K z m) :
    ContDiffAt ℝ ∞ (L.coefficients z).a x ∧
      ContDiffAt ℝ ∞ (L.coefficients z).b x ∧
      ContDiffAt ℝ ∞ (L.coefficients z).c x := by
  have hxann : x ∈ annularOpen D := (hA.domains z hz hs m).2.2.1 hx
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  obtain ⟨ha, hb, hc⟩ := hfield.smooth_coefficients z hz hs
  exact ⟨(ha x hxann).contDiffAt (hopen.mem_nhds hxann),
    (hb x hxann).contDiffAt (hopen.mem_nhds hxann),
    (hc x hxann).contDiffAt (hopen.mem_nhds hxann)⟩

/-- Complete the actual operator fields after the geometric construction and
the negative principal-density computation. No operator identity is assumed.
The resulting witness keeps exactly the supplied domains, charts and height. -/
theorem n04b_complete_geometric_atlas
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hcut : CanonicalCutGeometry S C K base ε)
    (htrans : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u → ∀ m θ,
        let Wl := canonicalHeight S K z (K.cutPair m).1 u
        let Wr := canonicalHeight S K z (K.cutPair m).2 u
        Wr (K.cutRadius m, θ) = Wl (K.cutRadius m, θ) ∧
        radialPartial Wr (K.cutRadius m, θ) =
          -radialPartial Wl (K.cutRadius m, θ) -
            Wl (K.cutRadius m, θ) / (2 * K.cutRadius m))
    (hprincipal : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m, K.positive m = false → ∀ x ∈ physicalPieceOpen S K z m,
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m)
          (K.height z m)).a x = 1 ∧
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m)
          (K.height z m)).b x = 0 ∧
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m)
          (K.height z m)).c x = -(K.chart z m x).1) :
    ∃ K' : CanonicalData S,
      N04PartA D S C K' base ε ∧ N04PartB S C L K' base ε := by
  let K₁ : CanonicalData S := n04bCanonicalOperatorData S L K
  refine ⟨n04bWithInteriorDivision C K₁,
    n04bWithInteriorDivision_partA (n04bCanonicalOperatorData_partA L hA), ?_⟩
  apply n04bWithInteriorDivision_partB_of_parts
  · exact hcut
  · exact htrans
  · exact n04bCanonicalOperatorData_operator_clause hA
      (fun z hz hs m x hx => n04b_field_contDiffAt_on_piece hA hfield hz hs m hx)
  · intro z hz hs m hm p hp
    have hcharts := hA.charts z hz hs m
    have hx : K.inverseChart z m p ∈ physicalPieceOpen S K z m :=
      hcharts.2.1 hp
    have hFx : K.chart z m (K.inverseChart z m p) = p :=
      hcharts.2.2.2.1 p hp
    have h := hprincipal z hz hs m hm (K.inverseChart z m p) hx
    simpa only [K₁, n04bCanonicalOperatorData,
      inverseChartPrincipalCoefficients, hFx] using h

end ContinuousFlexibility.Analysis
