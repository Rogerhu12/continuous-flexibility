import ContinuousFlexibility.Analysis.CanonicalActualReferenceGeometry

/-!
# Qualitative geometry for the supplied reference gauge

The caller supplies the original typed negative atlas, the radial
reference functions and their endpoint jets, and the same matched
relative family on one smaller neighborhood. The existing geometry
transport theorems are applied to that exact displayed atlas. No
reference functions, positive controls, cells or neighborhoods are
selected here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- Preserve the supplied order-four reference and order-three relative
matching throughout every qualitative geometry and transport clause. -/
theorem n04Realization_suppliedReferenceGeometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base newBase loss : ℕ} {ε η : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (K : CanonicalData S) (hK : K = n04bActualTypedAtlas hT hS hN hfield e₀)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi))
    (Y H₀ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (hreference : N04PositiveReferenceFamily K j 4 Y H₀)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (lower upper : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (hb : base ≤ newBase) (hη : 0 < η) (hηε : η ≤ ε)
    (hmatching : ∀ z ∈ stateNeighborhood S C newBase η, stateSector S z.1 → ∀ i,
      WholePositiveTransportMatching 3
        (fun side => n04PositiveSourceMap (j i side) K z)
        (fun side => n04PositiveSourceHeight (j i side) K z)
        (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (B.centerLeft i) (B.centerRight i) (lower i) (upper i))
    (href : ∀ i, τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => (1 : ℝ))) :
    let V : CanonicalData S := n04WholeReferenceGaugeAtlasData C L K e cell
      (fun i => positiveReferenceCylinderChart (Y i))
      (fun i => positiveReferenceCylinderInverse (Y i))
      (fun i p => H₀ i p.1) τ σ Q B.region
    N04PositiveReferenceFamily K j 4 Y H₀ ∧
      CanonicalGeometry D S C V newBase η ∧
      CanonicalCutOperatorProperties S C L V newBase η ∧
      CanonicalSourcePairing D S C V newBase η ∧
      CanonicalGeometry.ReferenceRadial S C V ∧
      CanonicalGeometry.TransmissionGeometry D S C V newBase η ∧
      ∀ z ∈ stateNeighborhood S C newBase η, stateSector S z.1 →
        WholeCanonicalTransportQualitative (D := D) C V z
          (n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id)
          (n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
            (fun _ => (1 : ℝ))) := by
  subst K
  let K : CanonicalData S := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint :=
    fun i => positiveReferenceCylinderChart (Y i)
  let χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint :=
    fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ :=
    fun i p => H₀ i p.1
  let W : CanonicalData S := n04WholeCanonicalAtlasData C L K e cell σ τ Q B.region
  let V : CanonicalData S := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q B.region
  have hrelative : ∀ z ∈ stateNeighborhood S C newBase η, stateSector S z.1 → ∀ i,
      WholePositiveChartGeometry (σ z i) (τ z i)
        (wholePositiveChartHeight (σ z i) (Q z i))
        (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i) :=
    fun z hz hs i => wholePositiveChartGeometry_of_matching (hmatching z hz hs i)
  have hW : CanonicalGeometry D S C W newBase η :=
    n04WholeCanonicalAtlasData_actual_geometry_restricted hT hS hN hfield
      e₀ e cell σ τ Q hb hη hηε B hrelative
  have hWcut : CanonicalCutOperatorProperties S C L W newBase η :=
    n04WholeCanonicalAtlasData_actual_cutOperator_restricted hT hS hN hfield
      e₀ e cell σ τ Q B.region hb hηε hW
  have hV : CanonicalGeometry D S C V newBase η :=
    n04WholeReferenceGaugeAtlasData_geometry C L K e cell ψ χ h₀ τ σ Q B.region
      hW (fun i => (hreference i).1) hrelative
  have hcutSource : CanonicalCutOperatorProperties S C L V newBase η ∧
      CanonicalSourcePairing D S C V newBase η :=
    n04WholeReferenceGaugeAtlasData_actual_cutOperator_and_sourcePairing
      hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q B.region hb hηε hWcut hV
  have hradial : CanonicalGeometry.ReferenceRadial S C V :=
    n04WholeReferenceGaugeAtlasData_actual_referenceRadial
      hT hS hN hfield e₀ e cell Y H₀ τ σ Q B.region hη href hV
  have htransmission : CanonicalGeometry.TransmissionGeometry D S C V newBase η :=
    n04WholeReferenceGaugeAtlasData_actual_transmissionGeometry
      hT hS hN hfield e₀ e cell Y H₀ τ σ Q B.region j
      (fun i => (hreference i).1)
      (fun i side θ a ha => (hreference i).2.1 side θ a (ha.trans (by decide)))
      (fun i side θ a ha => (hreference i).2.2 side θ a (ha.trans (by decide)))
      hb hη hηε (show 1 ≤ (3 : ℕ) by decide)
      B.centerLeft B.centerRight lower upper hmatching
  refine ⟨hreference, hV, hcutSource.1, hcutSource.2, hradial, htransmission, ?_⟩
  intro z hz hs
  have hglobal : WholeCanonicalTransportQualitative (D := D) C W z
      (n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id)
      (n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
        (fun _ => (1 : ℝ))) :=
    n04WholeCanonical_global_relative_transport_qualitative
      hT hS hN hfield e₀ e cell σ τ Q B.region j
      B.centerLeft B.centerRight lower upper
      (stateNeighborhood_mono S C hb hηε hz) hs (hmatching z hz hs)
      (fun i => ⟨(href i).2.1, (href i).2.2⟩)
  exact n04WholeReferenceGaugeAtlasData_global_transport
    C L K e cell ψ χ h₀ τ σ Q B.region z _ _ href
    (fun i => (hreference i).1.left_inverse)
    (fun i => (hmatching z hz hs i).geometry.left_inverse)
    (fun i p => ((hreference i).1.height_positive p).ne') hglobal

end ContinuousFlexibility.Analysis
