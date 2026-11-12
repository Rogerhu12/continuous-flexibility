import ContinuousFlexibility.Analysis.WholeCanonicalAtlasGeometry
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasCutOperator
import ContinuousFlexibility.Analysis.CanonicalNeighborhoodRestriction

/-!
# Restrict the state neighborhood while retaining the constructed atlas

The finite endpoint construction shrinks the state neighborhood. Its
positive fields need only have geometry on that smaller neighborhood.
The original typed atlas is retained, including every chosen negative
chart, inverse, height and reference cut; it is not reconstructed from
a restricted Through03 proof. All actual operator identities refer to
the same whole-atlas record on the smaller neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem n04WholeCanonicalAtlasData_actual_geometry_restricted
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base newBase loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (F G : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (hb : base ≤ newBase) (hε' : 0 < ε') (hε : ε' ≤ ε)
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi))
    (hpositive : ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ i,
      WholePositiveChartGeometry (F z i) (G z i)
        (wholePositiveChartHeight (F z i) (Q z i))
        (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i)) :
    CanonicalGeometry D S C
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q B.region) newBase ε' := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  have hsubState := stateNeighborhood_mono S C hb hε
  have hK : CanonicalGeometry D S C K newBase ε' :=
    n04PartA_restrict (n04b_actualTypedAtlas_partA hT hS hN hfield e₀) hb hε
  have hcut : CanonicalReferenceCutPairs S C K :=
    (n04bActualTypedAtlas_cutGeometry hT hS hN hfield e₀).1
  have hf : Continuous (deriv D.w) :=
    (n04b_profileGeometry_of_through03 hN).2.2.1.1.continuous_deriv (by simp)
  have hborder : RadialTrueBorder D := hN.1.1.1.2.2.2.1
  have hsub : B.region ⊆ K.normalizationRegion :=
    n04PositiveNormalizationBuffer_region_subset_actualNormalization
      hT hS hN hfield e₀ B hf
  refine {
    normalizationOpen := B.region_isOpen
    normalizationSupport := (support_referenceColumn_subset_tsupport_chi D).trans
      (B.support_subset_region hborder.2.2.1)
    normalization := fun z hz hs m => n04WholeCanonicalAtlasData_normalization
      C L K e cell F G Q B hK hf hsub
      ⟨reference_mem_stateNeighborhood S C newBase hε', hN.1.1.2.2.1.stateSector⟩
      hpositive hz hs m
    referenceBounds := n04WholeCanonicalAtlasData_referenceBounds
      C L K e cell F G Q B.region hK hf
    referencePositive := n04WholeCanonicalAtlasData_referencePositive
      C L K e cell F G Q B.region hf
    referenceNegative := n04WholeCanonicalAtlasData_referenceNegative
      C L K e cell F G Q B.region hK hcut
    referencePartition := n04WholeCanonicalAtlasData_actual_referencePartition
      hT hS hN hfield e₀ e cell F G Q B.region
    referenceDomain := n04WholeCanonicalAtlasData_referenceDomain
      C L K e cell F G Q B.region hK
    domains := fun z hz hs m => n04WholeCanonicalAtlasData_domains
      C L K e cell F G Q B.region hK hcut hf hz hs m
    partition := fun z hz hs => n04WholeCanonicalAtlasData_actual_partition
      hT hS hN hfield e₀ e cell F G Q B.region (hsubState hz) hs
    charts := fun z hz hs m => n04WholeCanonicalAtlasData_charts
      C L K e cell F G Q B.region hK hz hs (hpositive z hz hs) m
    boundary := fun z hz hs m => n04WholeCanonicalAtlasData_boundary
      C L K e cell F G Q B.region hK hz hs (hpositive z hz hs) hf m
    reflection := fun z hz hs m => n04WholeCanonicalAtlasData_reflection
      C L K e cell F G Q B.region hK hz hs (hpositive z hz hs) m
    inverseReflection := fun z hz hs m => n04WholeCanonicalAtlasData_inverseReflection
      C L K e cell F G Q B.region hK hz hs (hpositive z hz hs) m }

theorem n04WholeCanonicalAtlasData_actual_cutOperator_restricted
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base newBase loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (F G : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) (hb : base ≤ newBase) (hε : ε' ≤ ε)
    (hA : CanonicalGeometry D S C
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) newBase ε') :
    CanonicalCutOperatorProperties S C L
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q N) newBase ε' := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
  have hsubState := stateNeighborhood_mono S C hb hε
  have hfield' : N04bFieldRegularity D S C L newBase ε' :=
    { smooth_coefficients := fun z hz => hfield.smooth_coefficients z (hsubState hz)
      periodic_coefficients := fun z hz => hfield.periodic_coefficients z (hsubState hz)
      positive_a := fun z hz => hfield.positive_a z (hsubState hz)
      negative_discriminant := fun z hz => hfield.negative_discriminant z (hsubState hz) }
  have hcut := n04bActualTypedAtlas_cutGeometry hT hS hN hfield e₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact n04WholeCanonicalAtlasData_cutGeometry C L K e cell F G Q N
      ⟨hcut.1, fun z hz => hcut.2 z (hsubState hz)⟩
  · intro z hz hs u hu m θ
    exact n04WholeCanonicalAtlasData_transmission C L K e cell F G Q N
      (fun z hz hs u hu m θ => n04ActualAtlas_transmission
        hT hS hN hfield e₀ (hsubState hz) hs u hu m θ) hz hs u hu m θ
  · intro z hz hs m u hu p hp
    have hx := (hA.charts z hz hs m).2.1 hp
    obtain ⟨ha, hb, hc⟩ := n04b_field_contDiffAt_on_piece hA hfield' hz hs m hx
    have hop := n04b_canonicalOperator_explicit_fields hA hz hs m hp ha hb hc u hu
    have hf := n04WholeCanonicalAtlasData_actual_operatorFields
      hT hS hN hfield e₀ e cell F G Q N z m
    rw [← hf.1, ← hf.2 p] at hop
    exact hop
  · intro z hz hs m hm p hp
    have hx : W.inverseChart z m p ∈ physicalPieceOpen S W z m :=
      (hA.charts z hz hs m).2.1 hp
    have hFx : W.chart z m (W.inverseChart z m p) = p :=
      (hA.charts z hz hs m).2.2.2.1 p hp
    have hd := n04WholeCanonicalAtlasData_actual_negativePrincipalDensity
      hT hS hN hfield e₀ e cell F G Q N (hsubState hz) hs m hm _ hx
    have hf := n04WholeCanonicalAtlasData_actual_operatorFields
      hT hS hN hfield e₀ e cell F G Q N z m
    rw [hf.1]
    simpa only [inverseChartPrincipalCoefficients, hFx] using hd
  · intro z hz hs m hm p hp
    exact n04WholeCanonicalAtlasData_factorization C L K e cell F G Q N z m p hp

end ContinuousFlexibility.Analysis
