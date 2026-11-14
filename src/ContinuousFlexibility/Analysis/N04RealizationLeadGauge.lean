import ContinuousFlexibility.Analysis.CanonicalActualReferenceGeometry

/-!
# Geometry of the reference-gauged atlas for a supplied family

`n04Coordinates_exists_actual_reference_geometry` selects the reference
family and the positive transport family itself. Here both are supplied by
the caller: the reference interpolation `Y, H₀` with its family certificate,
and any positive transport family `τ, σ, Q` with the transport matching on a
smaller neighborhood and the identity at the reference state. The same
individual geometry, operator, radiality, transmission and global transport
lemmas then apply to the displayed atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04Realization_gaugeAtlas_of_family
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss newBase : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi))
    (Y H₀ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (hreference : N04PositiveReferenceFamily (n04bActualTypedAtlas hT hS hN hfield e₀) j 4 Y H₀)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) → N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (lower upper : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (hb : base ≤ newBase) (hε' : 0 < ε') (hε'ε : ε' ≤ ε)
    (hmatching : ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ i,
      WholePositiveTransportMatching 3
        (fun side => n04PositiveSourceMap (j i side) (n04bActualTypedAtlas hT hS hN hfield e₀) z)
        (fun side => n04PositiveSourceHeight (j i side)
          (n04bActualTypedAtlas hT hS hN hfield e₀) z)
        (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (B.centerLeft i) (B.centerRight i) (lower i) (upper i))
    (href : ∀ i, τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => (1 : ℝ))) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell
      (fun i => positiveReferenceCylinderChart (Y i))
      (fun i => positiveReferenceCylinderInverse (Y i))
      (fun i p => H₀ i p.1) τ σ Q B.region
    CanonicalGeometry D S C V newBase ε' ∧
      CanonicalCutOperatorProperties S C L V newBase ε' ∧
      CanonicalSourcePairing D S C V newBase ε' ∧
      CanonicalGeometry.ReferenceRadial S C V ∧
      CanonicalGeometry.TransmissionGeometry D S C V newBase ε' ∧
      ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
        WholeCanonicalTransportQualitative (D := D) C V z
          (n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id)
          (n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
            (fun _ => (1 : ℝ))) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H₀ i p.1
  let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q B.region
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q B.region
  have hrelative : ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ i,
      WholePositiveChartGeometry (σ z i) (τ z i)
        (wholePositiveChartHeight (σ z i) (Q z i))
        (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i) :=
    fun z hz hs i => wholePositiveChartGeometry_of_matching (hmatching z hz hs i)
  have hW : CanonicalGeometry D S C W newBase ε' :=
    n04WholeCanonicalAtlasData_actual_geometry_restricted hT hS hN hfield
      e₀ e cell σ τ Q hb hε' hε'ε B hrelative
  have hWcut : CanonicalCutOperatorProperties S C L W newBase ε' :=
    n04WholeCanonicalAtlasData_actual_cutOperator_restricted hT hS hN hfield
      e₀ e cell σ τ Q B.region hb hε'ε hW
  have hV : CanonicalGeometry D S C V newBase ε' :=
    n04WholeReferenceGaugeAtlasData_geometry C L K e cell ψ χ h₀ τ σ Q B.region
      hW (fun i => (hreference i).1) hrelative
  obtain ⟨hcut, hsource⟩ :=
    n04WholeReferenceGaugeAtlasData_actual_cutOperator_and_sourcePairing
      hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q B.region hb hε'ε hWcut hV
  have hradial : CanonicalGeometry.ReferenceRadial S C V :=
    n04WholeReferenceGaugeAtlasData_actual_referenceRadial
      hT hS hN hfield e₀ e cell Y H₀ τ σ Q B.region hε' href hV
  have htransmission : CanonicalGeometry.TransmissionGeometry D S C V newBase ε' :=
    n04WholeReferenceGaugeAtlasData_actual_transmissionGeometry
      hT hS hN hfield e₀ e cell Y H₀ τ σ Q B.region j
      (fun i => (hreference i).1)
      (fun i side θ a ha => (hreference i).2.1 side θ a (ha.trans (by decide)))
      (fun i side θ a ha => (hreference i).2.2 side θ a (ha.trans (by decide)))
      hb hε' hε'ε (show 1 ≤ (3 : ℕ) by decide) B.centerLeft B.centerRight
      lower upper hmatching
  refine ⟨hV, hcut, hsource, hradial, htransmission, ?_⟩
  intro z hz hs
  have hglobal : WholeCanonicalTransportQualitative (D := D) C W z
      (n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id)
      (n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
        (fun _ => (1 : ℝ))) :=
    n04WholeCanonical_global_relative_transport_qualitative
      hT hS hN hfield e₀ e cell σ τ Q B.region j B.centerLeft B.centerRight
      lower upper
      (stateNeighborhood_mono S C hb hε'ε hz) hs (hmatching z hz hs)
      (fun i => ⟨(href i).2.1, (href i).2.2⟩)
  exact n04WholeReferenceGaugeAtlasData_global_transport
    C L K e cell ψ χ h₀ τ σ Q B.region z _ _ href
    (fun i => (hreference i).1.left_inverse)
    (fun i => (hmatching z hz hs i).geometry.left_inverse)
    (fun i p => ((hreference i).1.height_positive p).ne') hglobal

end ContinuousFlexibility.Analysis
