module

public import ContinuousFlexibility.Analysis.N04RealizationMaterialJets
public import ContinuousFlexibility.Analysis.N04RealizationJetCompletion
public import ContinuousFlexibility.Analysis.N04RealizationTransportJets
public import ContinuousFlexibility.Analysis.CanonicalNeighborhoodRestriction
public import ContinuousFlexibility.Analysis.N06Neighborhood

/-!
# Completing the retained coordinate witness on one neighborhood

The primitive reference and current towers give the quantitative N04 clause.
The actual sample displacement gives the material certificate, and the
constructed global transport gives the transport certificate. Their common
restriction retains every preceding nonlinear property and all six primitive
geometry clauses for the same normalized coordinate data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
  CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- All four final payloads use the supplied records and one common
neighborhood. Only the unused operator values are normalized, and the fixed
loss may increase to retain the earlier nonlinear bounds. -/
theorem n04Realization_sameWitnessCompletion
    (hT : IsMaterialData D T)
    (hthrough : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hprimitive : PrimitiveGeometryProperties D T S C L K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hfloor : ∀ r : ℝ, 1 ≤ T.E0 r)
    (hqual : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ τ : PolarPoint → PolarPoint, ∃ q : PolarPoint → ℝ,
        WholeCanonicalTransportQualitative (D := D) C K z τ q)
    (hshift : ∃ B : ℝ, 0 ≤ B ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ m x, x ∈ physicalPieceOpen S K z m →
          endpointX 1 (Statements.endpointDistance D (T.sample (K.cell m))) ≤
            endpointX 1 (Statements.endpointDistance D x.1) + B) :
    ∃ base' loss' : ℕ, base ≤ base' ∧ loss ≤ loss' ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
        NonlinearPropertiesThrough03 D T S C R L base' loss' η ∧
        N04Properties D T S C L (normalizedCanonicalData S K) base' loss' η ∧
        PrimitiveGeometryProperties D T S C L
          (normalizedCanonicalData S K) base' η ∧
        CanonicalPrimitiveGeometry D T S C L
          (normalizedCanonicalData S K) base' η := by
  have hN : N01Properties D T S C base loss ε := hthrough.1.1
  have hD : IsAccumulatingProfile D := hN.1.1
  have hε : 0 < ε := hN.2.1
  have hrefState : referenceStateConditions D S C := hN.2.2.1
  obtain ⟨d, hd, h04⟩ := n04Realization_exists_normalized_properties_of_primitive
    hD hT hrefState hA hB hprimitive.2.2.1 hprimitive.2.2.2.1
      (fun m => hfloor (T.sample (K.cell m))) loss
  have hprimitive' : PrimitiveGeometryProperties D T S C L
      (normalizedCanonicalData S K) base ε :=
    n04Realization_primitiveGeometryProperties_normalized hrefState hprimitive
  have hqual' : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ τ : PolarPoint → PolarPoint, ∃ q : PolarPoint → ℝ,
        WholeCanonicalTransportQualitative (D := D) C
          (normalizedCanonicalData S K) z τ q := hqual
  obtain ⟨bm, hbm, ηm, hηm, hηmε, hmaterial⟩ :=
    n04Realization_materialJets_neighborhood hD hT hε hrefState h04.1
      hprimitive'.2.2.1 hprimitive'.2.2.2.1 hfloor hshift
  obtain ⟨bt, hbt, ηt, hηt, hηtε, htransport⟩ :=
    n04Realization_transport_neighborhood hD hT hε (fun r _ => hfloor r)
      hrefState h04 hprimitive'.2.2.1 hprimitive'.2.2.2.1 hqual'
  let b : ℕ := max bm bt
  let η : ℝ := min ηm ηt
  have hbm' : bm ≤ b := le_max_left _ _
  have hbt' : bt ≤ b := le_max_right _ _
  have hb : base ≤ b := hbm.trans hbm'
  have hηm' : η ≤ ηm := min_le_left _ _
  have hηt' : η ≤ ηt := min_le_right _ _
  have hη : 0 < η := lt_min hηm hηt
  have hηε : η ≤ ε := hηm'.trans hηmε
  have hUm : stateNeighborhood S C b η ⊆ stateNeighborhood S C bm ηm :=
    stateNeighborhood_mono S C hbm' hηm'
  have hUt : stateNeighborhood S C b η ⊆ stateNeighborhood S C bt ηt :=
    stateNeighborhood_mono S C hbt' hηt'
  have hU : stateNeighborhood S C b η ⊆ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hb hηε
  choose r degree B A hBpos hAnonneg hbound using hmaterial
  refine ⟨b, d, hb, hd, η, hη, hηε,
    nonlinearPropertiesThrough03_restrict hT hthrough hb hd hη hηε,
    n06_N04Properties_mono h04 hb hηε,
    n07a_primitiveGeometry_restrict hD hT hprimitive' hb hηε, ?_⟩
  exact
    { materialJets := fun N => ⟨r N, degree N, B N, A N, hBpos N, hAnonneg N,
        fun z hz => hbound N z (hUm hz)⟩
      transport := fun z hz => htransport z (hUt hz)
      physicalCoefficients := fun z hz =>
        n04Coordinates_physicalCoefficients_of_fieldRegularity hfield z (hU hz) }

end ContinuousFlexibility.Analysis
