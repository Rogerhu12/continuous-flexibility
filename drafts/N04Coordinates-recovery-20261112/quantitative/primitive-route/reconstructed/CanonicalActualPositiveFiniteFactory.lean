import ContinuousFlexibility.Analysis.CanonicalPositiveFiniteEndpointBounds
import ContinuousFlexibility.Analysis.N04bActualAtlasInteriorCompletion

/-!
# The actual whole-positive family with its endpoint inputs derived

The original typed atlas is kept after the common state neighborhood is
shrunk. The preliminary interior completion changes no source map or
height. Actual endpoint bounds then feed the existing finite family
constructor, with one inverse-fiber constant and one height collar for
all states. The normalization-buffer centers remain free ordered inputs.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The original actual typed atlas, without rebuilding it on the smaller
neighborhood, satisfies the six finite endpoint input clauses. -/
theorem n04Coordinates_actual_positiveEndpoint_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (n : ℕ) :
    ∃ newBase : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ j : ∀ side, N04PositiveEndpointSource C i side,
      ∃ κ M H : ℝ, 0 < κ ∧ κ ≤ 1 ∧ κ⁻¹ ≤ M ∧ 1 ≤ M ∧ 1 ≤ H ∧
        ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
          let K := n04bActualTypedAtlas hT hS hN hfield e
          WholePositiveEndpointJetBounds n
            (fun side => n04PositiveSourceMap (j side) K z)
            (fun side => n04PositiveSourceHeight (j side) K z)
            (n04PositiveLeft i) (n04PositiveRight i) κ κ M H := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hA := n04bWithInteriorDivision_partA
    (n04b_actualTypedAtlas_partA hT hS hN hfield e)
  have hB := n04bActualTypedAtlas_interiorCompletion_partB hT hS hN hfield e
  have hfinite := n04b_exists_common_positive_endpoint_bounds hS hT hN hfield hA hB n
  simpa only [n04PositiveSourceMap, n04PositiveSourceHeight,
    canonicalCurrentPoint, n04CoordinatesCurrentHeightRatio, n04bWithInteriorDivision]
    using hfinite

/-- No endpoint-bound hypothesis remains. The common base and radius
precede all components. Each component then selects finite envelopes,
and any ordered buffer centers give the actual common family. -/
theorem n04Coordinates_exists_actual_wholePositive_families
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (n : ℕ) :
    ∃ newBase : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ j : ∀ side, N04PositiveEndpointSource C i side,
      ∃ κ M H : ℝ, 0 < κ ∧ κ ≤ 1 ∧ κ⁻¹ ≤ M ∧ 1 ≤ M ∧ 1 ≤ H ∧
      ∀ c d : ℝ, n04PositiveLeft i < c → c < d → d < n04PositiveRight i →
        let l := n04PositiveLeft i
        let r := n04PositiveRight i
        let ρ := min ((r - l) / 4) (min (c - l) (r - d))
        ∃ Clog Mσ δ : ℝ, 0 < Clog ∧ 1 ≤ Mσ ∧ 0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧
          δ⁻¹ = ρ⁻¹ + 1 + ((n + 1 : ℕ) : ℝ) * (Clog * H ^ (2 * n + 1) + 1) ∧
          0 < endpointFiberLower n l r c d κ Mσ ∧
          ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
            let K := n04bActualTypedAtlas hT hS hN hfield e
            let F := fun side => n04PositiveSourceMap (j side) K z
            let q := fun side => n04PositiveSourceHeight (j side) K z
            let ψ := fun side p => (F side p).2
            let X := fun side p => (F side p).1
            let τ := oneSidedWholeComponentTransport n ψ X l r c d κ κ M Mσ
            let σ := oneSidedWholeComponentTransportInverse n ψ X l r c d κ κ M Mσ
            let Q := positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q
            WholePositiveTransportMatching n F q τ σ Q l r c d
              (endpointFiberLower n l r c d κ Mσ * (κ / 2)) (Real.exp 2 * H ^ 2) ∧
              (z = (C.referenceState, 0) → τ = id ∧ σ = id ∧ Q = (fun _ => (1 : ℝ))) := by
  obtain ⟨newBase, ε', hb, hε', hε'ε, hfinite⟩ :=
    n04Coordinates_actual_positiveEndpoint_bounds hT hS hN hfield e n
  refine ⟨newBase, ε', hb, hε', hε'ε, ?_⟩
  intro i j
  obtain ⟨κ, M, H, hκ, hκone, hκinv, hM, hH, hbounds⟩ := hfinite i j
  refine ⟨κ, M, H, hκ, hκone, hκinv, hM, hH, ?_⟩
  intro c d hlc hcd hdr
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let Z := {z : AnnularState S × ℝ //
    z ∈ stateNeighborhood S C newBase ε' ∧ stateSector S z.1}
  let z₀ : Z := ⟨(C.referenceState, 0),
    reference_mem_stateNeighborhood S C newBase hε', hN.1.1.2.2.1.stateSector⟩
  let a : Bool → ℝ := fun side => n04PositiveSourceLeft (j side)
  let b : Bool → ℝ := fun side => n04PositiveSourceRight (j side)
  let F : Z → Bool → PolarPoint → PolarPoint := fun z side => n04PositiveSourceMap (j side) K z.1
  let q : Z → Bool → PolarPoint → ℝ := fun z side => n04PositiveSourceHeight (j side) K z.1
  have hdata (z : Z) (side : Bool) :
      OneSidedTransportEndpoint (F z side) (q z side) (a side) (b side)
        (if side then n04PositiveRight i else n04PositiveLeft i) :=
    n04Coordinates_actualAtlas_positiveEndpoint_of_source hT hS hN hfield e (j side)
      (stateNeighborhood_mono S C hb hε'ε z.2.1) z.2.2
  have hf (z : Z) : WholePositiveEndpointJetBounds n (F z) (q z)
      (n04PositiveLeft i) (n04PositiveRight i) κ κ M H :=
    hbounds z.1 z.2.1 z.2.2
  have href (side : Bool) (θ : ℝ) :
      F z₀ side =ᶠ[𝓝 (if side then n04PositiveRight i else n04PositiveLeft i, θ)]
          (id : PolarPoint → PolarPoint) ∧
        q z₀ side =ᶠ[𝓝 (if side then n04PositiveRight i else n04PositiveLeft i, θ)]
          (fun _ => (1 : ℝ)) :=
    n04Coordinates_positiveSource_reference_germs hT hS hN hfield e (j side) θ
  have hout := exists_wholePositiveTransport_family (F := F) (q := q) (a := a) (b := b)
    (l := n04PositiveLeft i) (r := n04PositiveRight i) z₀ n
    hlc hcd hdr hκ hκone hκ (zero_le_one.trans hM) hH hdata
    (fun z => (hf z).angular_lower) (fun z => (hf z).radial_lower)
    (fun z => (hf z).coordinate_jets) (fun z => (hf z).height_value)
    (fun z => (hf z).height_inverse) (fun z => (hf z).height_jets) href
  dsimp only at hout ⊢
  rcases hout with ⟨Clog, Mσ, δ, hClog, hMσ, hδ, hδρ, hδone, hrecip, hB, hout⟩
  refine ⟨Clog, Mσ, δ, hClog, hMσ, hδ, hδρ, hδone, hrecip, hB, ?_⟩
  intro z hz hs
  let z' : Z := ⟨z, hz, hs⟩
  have hzout := hout z'
  refine ⟨hzout.1, ?_⟩
  intro he
  exact hzout.2 (Subtype.ext he)

end ContinuousFlexibility.Analysis
