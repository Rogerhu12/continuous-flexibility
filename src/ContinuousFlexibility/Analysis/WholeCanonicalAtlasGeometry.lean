import ContinuousFlexibility.Analysis.WholeCanonicalAtlasChartGeometry
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasDomainFields
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasNormalization
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasReferencePartition
import ContinuousFlexibility.Analysis.N04bActualAtlasCuts
import ContinuousFlexibility.Analysis.N01NormalizationRootSeparation

/-!
# Complete geometry of the actual whole-component atlas

Keep the already constructed negative charts on their genuine moving
domains. Insert the actual whole positive transports into the same one
record, with a reference-only buffered normalization set. The complete
geometry follows from those actual fields and both proved partitions.
No canonical primitive estimate is a hypothesis of this assembly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04WholeCanonicalAtlasData_actual_geometry
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
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi))
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ i,
      WholePositiveChartGeometry (F z i) (G z i)
        (wholePositiveChartHeight (F z i) (Q z i))
        (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i)) :
    CanonicalGeometry D S C
      (n04WholeCanonicalAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell F G Q B.region) base ε := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  have hK : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e₀
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
      C L K e cell F G Q B hK hf hsub (n04b_reference_valid_of_through03 hN)
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
      hT hS hN hfield e₀ e cell F G Q B.region hz hs
    charts := fun z hz hs m => n04WholeCanonicalAtlasData_charts
      C L K e cell F G Q B.region hK hz hs (hpositive z hz hs) m
    boundary := fun z hz hs m => n04WholeCanonicalAtlasData_boundary
      C L K e cell F G Q B.region hK hz hs (hpositive z hz hs) hf m
    reflection := fun z hz hs m => n04WholeCanonicalAtlasData_reflection
      C L K e cell F G Q B.region hK hz hs (hpositive z hz hs) m
    inverseReflection := fun z hz hs m => n04WholeCanonicalAtlasData_inverseReflection
      C L K e cell F G Q B.region hK hz hs (hpositive z hz hs) m }

end ContinuousFlexibility.Analysis
