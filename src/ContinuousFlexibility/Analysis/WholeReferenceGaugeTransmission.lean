module

public import ContinuousFlexibility.Analysis.WholeReferenceGaugeRootMatching

/-!
# Root and cut transmission of the same reference-gauged atlas

The actual physical-interface classification and actual middle-cut jets
are independent of the positive reference gauge. The cut result is
restricted to the smaller neighborhood while retaining the original K.
Together with the separately proved raw root matching, they give the
three clauses of the transmission predicate for the same record.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04WholeReferenceGaugeAtlasData_actual_transmissionGeometry_of_root
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss newBase : ℕ} {ε ε' : ℝ}
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
    (N : Set ℝ) (hb : base ≤ newBase) (hε'ε : ε' ≤ ε)
    (hroot : CanonicalGeometry.RootFirstJetMatching D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell ψ χ h₀ τ σ Q N) newBase ε') :
    CanonicalGeometry.TransmissionGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell ψ χ h₀ τ σ Q N) newBase ε' := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  have hcut := n04Coordinates_actualAtlas_cutFirstJetMatching hT hS hN hfield e₀
  have hcutRestricted : CanonicalGeometry.CutFirstJetMatching S C K newBase ε' := by
    intro m z hz θ
    apply hcut m z ?_ θ
    rcases hz with href | hz
    · exact Or.inl href
    · exact Or.inr ⟨stateNeighborhood_mono S C hb hε'ε hz.1, hz.2⟩
  exact ⟨n04WholeReferenceGaugeAtlasData_actual_interfaceClassification
      hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N,
    hroot, n04WholeReferenceGaugeAtlasData_cutFirstJetMatching
      C L K e cell ψ χ h₀ τ σ Q N hcutRestricted⟩

/-- Full transmission for the actual reference interpolation and the same
selected relative family on the smaller neighborhood. -/
theorem n04WholeReferenceGaugeAtlasData_actual_transmissionGeometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss newBase n : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hYjets : ∀ i side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => Y i p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceCoordinate (j i side)
          (n04bActualTypedAtlas hT hS hN hfield e₀)) (n04PositiveEndpoint i side, θ))
    (hHjets : ∀ i side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => H i p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceHeight (j i side)
          (n04bActualTypedAtlas hT hS hN hfield e₀)) (n04PositiveEndpoint i side, θ))
    (hb : base ≤ newBase) (hε' : 0 < ε') (hε'ε : ε' ≤ ε) (hn : 1 ≤ n)
    (c d J Hbound : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (hmatching : ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ i,
      WholePositiveTransportMatching n
        (fun side => n04PositiveSourceMap (j i side)
          (n04bActualTypedAtlas hT hS hN hfield e₀) z)
        (fun side => n04PositiveSourceHeight (j i side)
          (n04bActualTypedAtlas hT hS hN hfield e₀) z)
        (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (c i) (d i) (J i) (Hbound i)) :
    CanonicalGeometry.TransmissionGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i)) (fun i p => H i p.1) τ σ Q N)
      newBase ε' := by
  have hroot := n04WholeReferenceGaugeAtlasData_actual_rootFirstJetMatching
    hT hS hN hfield e₀ e cell Y H τ σ Q N j hgeometry hYjets hHjets
    hb hε' hε'ε hn c d J Hbound hmatching
  exact n04WholeReferenceGaugeAtlasData_actual_transmissionGeometry_of_root
    hT hS hN hfield e₀ e cell
    (fun i => positiveReferenceCylinderChart (Y i))
    (fun i => positiveReferenceCylinderInverse (Y i))
    (fun i p => H i p.1) τ σ Q N hb hε'ε hroot

end ContinuousFlexibility.Analysis
