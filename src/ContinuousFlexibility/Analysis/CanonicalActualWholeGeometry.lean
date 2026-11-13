import ContinuousFlexibility.Analysis.CanonicalFixedPositiveFamily
import ContinuousFlexibility.Analysis.WholeCanonicalAtlasRestrictedGeometry
import ContinuousFlexibility.Analysis.WholeCanonicalGlobalReferenceAgreement
import ContinuousFlexibility.Analysis.CanonicalSourceConversion

/-!
# Actual whole-atlas geometry without an endpoint-bound premise

The fixed degree-three positive construction and the original negative
atlas form one whole atlas. The smaller neighborhood restricts the old
data without choosing it again. The same record has geometry, the actual
operator and source pairing, and one global qualitative relative map.
The exact positive parameters and matching are retained for the separate
quantitative proof.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

def WholeCanonicalTransportQualitative
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (W : CanonicalData S)
    (z : AnnularState S × ℝ) (F : PolarPoint → PolarPoint) (q : PolarPoint → ℝ) : Prop :=
  ContDiffOn ℝ 3 F (annularOpen D) ∧ ContDiffOn ℝ 3 q (annularOpen D) ∧
    MapsTo F (annularOpen D) (annularOpen D) ∧
    (∀ p, F (p + (0, Real.pi)) = F p + (0, Real.pi)) ∧
    Function.Periodic q (0, Real.pi) ∧
    (∀ p, F (p.1, -p.2) = ((F p).1, -(F p).2)) ∧
    (∀ r θ, q (r, -θ) = q (r, θ)) ∧
    (∀ m, ∀ p ∈ referencePhysicalPieceOpen S W m,
      F p = canonicalCurrentPoint C W z m p ∧
        q p = W.height (C.referenceState, 0) m p / W.height z m (F p)) ∧
    ∀ p ∈ annularOpen D, 0 < q p

/-- Finite endpoint controls are derived from the original hypotheses.
Every later clause uses the same displayed maps, widths and atlas. -/
theorem n04Coordinates_exists_actual_whole_geometry_with_log_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi)) :
    ∃ newBase : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∃ κ M H Clog Mσ δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ,
        N04FixedPositiveFamilyControls B 3 κ M H Clog Mσ δ ∧
        let K := n04bActualTypedAtlas hT hS hN hfield e₀
        let τ := n04FixedPositiveTransport K j B 3 κ M Mσ
        let σ := n04FixedPositiveInverse K j B 3 κ M Mσ
        let Q := n04FixedPositiveHeight K j 3 δ
        let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q B.region
        (∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
          ∀ i side k, 0 < k → k ≤ 3 → ∀ θ,
            |positiveHeightTaylorData (n04PositiveLeft i) (n04PositiveRight i) (fun _ => 1)
              (fun side => n04PositiveSourceHeight (j i side) K z) side k θ| ≤
              Clog i * H i ^ 7) ∧
        (∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ i,
          WholePositiveTransportMatching 3
            (fun side => n04PositiveSourceMap (j i side) K z)
            (fun side => n04PositiveSourceHeight (j i side) K z)
            (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
            (B.centerLeft i) (B.centerRight i)
            (endpointFiberLower 3 (n04PositiveLeft i) (n04PositiveRight i)
              (B.centerLeft i) (B.centerRight i) (κ i) (Mσ i) * (κ i / 2))
            (Real.exp 2 * H i ^ 2)) ∧
          CanonicalGeometry D S C W newBase ε' ∧
          CanonicalCutOperatorProperties S C L W newBase ε' ∧
          CanonicalSourcePairing D S C W newBase ε' ∧
          ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
            WholeCanonicalTransportQualitative (D := D) C W z
              (n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id)
              (n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
                (fun _ => (1 : ℝ))) := by
  obtain ⟨newBase, ε', hb, hε', hε'ε, κ, M, H, Clog, Mσ, δ,
      hcontrols, hlog, hmatching, href⟩ :=
    n04Coordinates_exists_fixed_positive_family_with_log_bounds hT hS hN hfield e₀ j B 3
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let τ := n04FixedPositiveTransport K j B 3 κ M Mσ
  let σ := n04FixedPositiveInverse K j B 3 κ M Mσ
  let Q := n04FixedPositiveHeight K j 3 δ
  let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q B.region
  have hA : CanonicalGeometry D S C W newBase ε' :=
    n04WholeCanonicalAtlasData_actual_geometry_restricted hT hS hN hfield
      e₀ e cell σ τ Q hb hε' hε'ε B
      (fun z hz hs i => wholePositiveChartGeometry_of_matching (hmatching z hz hs i))
  have hcut : CanonicalCutOperatorProperties S C L W newBase ε' :=
    n04WholeCanonicalAtlasData_actual_cutOperator_restricted hT hS hN hfield
      e₀ e cell σ τ Q B.region hb hε'ε hA
  refine ⟨newBase, ε', hb, hε', hε'ε, κ, M, H, Clog, Mσ, δ,
    hcontrols, hlog, hmatching, hA, hcut, ?_, ?_⟩
  · intro z hz hs m u f _ _ _ _ _ _
    exact canonicalSource_pairing_of_partA hA hz hs m u f
  · intro z hz hs
    exact n04WholeCanonical_global_relative_transport_qualitative
      hT hS hN hfield e₀ e cell σ τ Q B.region j
      B.centerLeft B.centerRight
      (fun i => endpointFiberLower 3 (n04PositiveLeft i) (n04PositiveRight i)
        (B.centerLeft i) (B.centerRight i) (κ i) (Mσ i) * (κ i / 2))
      (fun i => Real.exp 2 * H i ^ 2)
      (stateNeighborhood_mono S C hb hε'ε hz) hs (hmatching z hz hs)
      (fun i => ⟨(href i).2.1, (href i).2.2⟩)

/-- Projection of the retained construction to the original interface. -/
theorem n04Coordinates_exists_actual_whole_geometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi)) :
    ∃ newBase : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∃ κ M H Clog Mσ δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ,
        N04FixedPositiveFamilyControls B 3 κ M H Clog Mσ δ ∧
        let K := n04bActualTypedAtlas hT hS hN hfield e₀
        let τ := n04FixedPositiveTransport K j B 3 κ M Mσ
        let σ := n04FixedPositiveInverse K j B 3 κ M Mσ
        let Q := n04FixedPositiveHeight K j 3 δ
        let W := n04WholeCanonicalAtlasData C L K e cell σ τ Q B.region
        (∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ i,
          WholePositiveTransportMatching 3
            (fun side => n04PositiveSourceMap (j i side) K z)
            (fun side => n04PositiveSourceHeight (j i side) K z)
            (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
            (B.centerLeft i) (B.centerRight i)
            (endpointFiberLower 3 (n04PositiveLeft i) (n04PositiveRight i)
              (B.centerLeft i) (B.centerRight i) (κ i) (Mσ i) * (κ i / 2))
            (Real.exp 2 * H i ^ 2)) ∧
          CanonicalGeometry D S C W newBase ε' ∧
          CanonicalCutOperatorProperties S C L W newBase ε' ∧
          CanonicalSourcePairing D S C W newBase ε' ∧
          ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
            WholeCanonicalTransportQualitative (D := D) C W z
              (n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id)
              (n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
                (fun _ => (1 : ℝ))) := by
  obtain ⟨newBase, ε', hb, hε', hε'ε, κ, M, H, Clog, Mσ, δ,
      hcontrols, _hlog, hmatching, hA, hcut, hpairing, htransport⟩ :=
    n04Coordinates_exists_actual_whole_geometry_with_log_bounds hT hS hN hfield e₀ e cell j B
  exact ⟨newBase, ε', hb, hε', hε'ε, κ, M, H, Clog, Mσ, δ,
    hcontrols, hmatching, hA, hcut, hpairing, htransport⟩

end ContinuousFlexibility.Analysis
