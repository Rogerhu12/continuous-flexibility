import ContinuousFlexibility.Analysis.CanonicalActualWholeGeometry

/-!
# Geometry for the supplied whole-component family

The positive family, its reference identities, and its material labels
are supplied by the caller. The negative atlas is identified with the
original typed construction before any restriction of the neighborhood.
The existing geometry, operator and global transport theorems then apply
to precisely that whole atlas. No component controls are selected here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- The caller's matching family gives all qualitative atlas clauses on
its one supplied neighborhood. The original typed-atlas identity and all
three reference identities remain in the returned certificate. -/
theorem n04Realization_wholeAtlas_of_matching
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
    (σ τ : (AnnularState S × ℝ) →
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
    let W : CanonicalData S := n04WholeCanonicalAtlasData C L K e cell σ τ Q B.region
    K = n04bActualTypedAtlas hT hS hN hfield e₀ ∧
      (∀ i, τ (C.referenceState, 0) i = id ∧
        σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => (1 : ℝ))) ∧
      NonlinearPropertiesThrough03 D T S C R L newBase loss η ∧
      N04bFieldRegularity D S C L newBase η ∧
      N04PartA D S C W newBase η ∧ N04PartB S C L W newBase η ∧
      CanonicalSourcePairing D S C W newBase η ∧
      ∀ z ∈ stateNeighborhood S C newBase η, stateSector S z.1 →
        WholeCanonicalTransportQualitative (D := D) C W z
          (n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id)
          (n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
            (fun _ => (1 : ℝ))) := by
  subst K
  let K : CanonicalData S := n04bActualTypedAtlas hT hS hN hfield e₀
  let W : CanonicalData S := n04WholeCanonicalAtlasData C L K e cell σ τ Q B.region
  have hsub : stateNeighborhood S C newBase η ⊆ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hb hηε
  have hA : N04PartA D S C W newBase η :=
    n04WholeCanonicalAtlasData_actual_geometry_restricted hT hS hN hfield
      e₀ e cell σ τ Q hb hη hηε B
      (fun z hz hs i => wholePositiveChartGeometry_of_matching (hmatching z hz hs i))
  have hcut : N04PartB S C L W newBase η :=
    n04WholeCanonicalAtlasData_actual_cutOperator_restricted hT hS hN hfield
      e₀ e cell σ τ Q B.region hb hηε hA
  refine ⟨rfl, href,
    nonlinearPropertiesThrough03_restrict hT hN hb le_rfl hη hηε,
    ?_, hA, hcut, ?_, ?_⟩
  · exact
      { smooth_coefficients := fun z hz => hfield.smooth_coefficients z (hsub hz)
        periodic_coefficients := fun z hz => hfield.periodic_coefficients z (hsub hz)
        positive_a := fun z hz => hfield.positive_a z (hsub hz)
        negative_discriminant := fun z hz => hfield.negative_discriminant z (hsub hz)
        reference_flow := hfield.reference_flow }
  · intro z hz hs m u f _ _ _ _ _ _
    exact canonicalSource_pairing_of_partA hA hz hs m u f
  · intro z hz hs
    exact n04WholeCanonical_global_relative_transport_qualitative
      hT hS hN hfield e₀ e cell σ τ Q B.region j
      B.centerLeft B.centerRight lower upper (hsub hz) hs (hmatching z hz hs)
      (fun i => ⟨(href i).2.1, (href i).2.2⟩)

end ContinuousFlexibility.Analysis
