import ContinuousFlexibility.Analysis.CanonicalReferenceTransportGerms
import ContinuousFlexibility.Analysis.WholePositiveTransportAssembly

/-!
# The actual whole-positive-component transport from finite endpoint data

Only finitely many ordinary jets of the actual stored endpoint fields
are bounded as inputs. The one-sided geometry, angular symmetries and
reference identity germs are derived from the actual atlas factory.
The certified endpoint source is fixed before the state; an ambient
endpoint is allowed and contributes identity/one.

The common constants below are an interface for the separate material
endpoint estimates. No global transport, positive atlas, or primitive
bound is an assumption of this finite construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

structure WholePositiveEndpointJetBounds (n : ℕ)
    (F : Bool → PolarPoint → PolarPoint) (q : Bool → PolarPoint → ℝ)
    (l r κφ κX M H : ℝ) : Prop where
  angular_lower : ∀ side θ, κφ ≤ angularPartial (fun p => (F side p).2)
    (if side then r else l, θ)
  radial_lower : ∀ side θ, κX ≤ radialPartial (fun p => (F side p).1)
    (if side then r else l, θ)
  coordinate_jets : ∀ side k, 1 ≤ k → k ≤ n + 2 → ∀ θ,
    ‖iteratedFDeriv ℝ k (F side) (if side then r else l, θ)‖ ≤ M
  height_value : ∀ side θ, q side (if side then r else l, θ) ≤ H
  height_inverse : ∀ side θ, (q side (if side then r else l, θ))⁻¹ ≤ H
  height_jets : ∀ side k, 1 ≤ k → k ≤ n → ∀ θ,
    ‖iteratedFDeriv ℝ k (q side) (if side then r else l, θ)‖ ≤ H

theorem n04Coordinates_wholePositive_transport_of_endpoint_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (n : ℕ) (i : N04PositiveComponent D.a D.b (deriv D.w))
    (j : ∀ side, N04PositiveEndpointSource C i side)
    {c d κφ κX M H : ℝ}
    (hlc : n04PositiveLeft i < c) (hcd : c < d) (hdr : d < n04PositiveRight i)
    (hκφ : 0 < κφ) (hκφone : κφ ≤ 1) (hκX : 0 < κX) (hM : 0 ≤ M) (hH : 1 ≤ H)
    (hbound : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      let K := n04bActualTypedAtlas hT hS hN hfield e
      WholePositiveEndpointJetBounds n
        (fun side => n04PositiveSourceMap (j side) K z)
        (fun side => n04PositiveSourceHeight (j side) K z)
        (n04PositiveLeft i) (n04PositiveRight i) κφ κX M H) :
    let l := n04PositiveLeft i
    let r := n04PositiveRight i
    let ρ := min ((r - l) / 4) (min (c - l) (r - d))
    ∃ Clog Mσ δ : ℝ, 0 < Clog ∧ 1 ≤ Mσ ∧ 0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧
      δ⁻¹ = ρ⁻¹ + 1 + ((n + 1 : ℕ) : ℝ) * (Clog * H ^ (2 * n + 1) + 1) ∧
      0 < endpointFiberLower n l r c d κX Mσ ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      let K := n04bActualTypedAtlas hT hS hN hfield e
      let F := fun side => n04PositiveSourceMap (j side) K z
      let q := fun side => n04PositiveSourceHeight (j side) K z
      let ψ := fun side p => (F side p).2
      let X := fun side p => (F side p).1
      let τ := oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ
      let σ := oneSidedWholeComponentTransportInverse n ψ X l r c d κφ κX M Mσ
      let Q := positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q
      WholePositiveTransportMatching n F q τ σ Q l r c d
        (endpointFiberLower n l r c d κX Mσ * (κφ / 2)) (Real.exp 2 * H ^ 2) ∧
        (z = (C.referenceState, 0) → τ = id ∧ σ = id ∧ Q = (fun _ => (1 : ℝ))) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let Z := {z : AnnularState S × ℝ //
    z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1}
  let z₀ : Z := ⟨(C.referenceState, 0),
    reference_mem_stateNeighborhood S C base hN.1.1.2.1, hN.1.1.2.2.1.stateSector⟩
  let a : Bool → ℝ := fun side => n04PositiveSourceLeft (j side)
  let b : Bool → ℝ := fun side => n04PositiveSourceRight (j side)
  let F : Z → Bool → PolarPoint → PolarPoint := fun z side =>
    n04PositiveSourceMap (j side) K z.1
  let q : Z → Bool → PolarPoint → ℝ := fun z side =>
    n04PositiveSourceHeight (j side) K z.1
  have hdata (z : Z) (side : Bool) :
      OneSidedTransportEndpoint (F z side) (q z side) (a side) (b side)
        (if side then n04PositiveRight i else n04PositiveLeft i) :=
    n04Coordinates_actualAtlas_positiveEndpoint_of_source
      hT hS hN hfield e (j side) z.2.1 z.2.2
  have hfinite (z : Z) : WholePositiveEndpointJetBounds n (F z) (q z)
      (n04PositiveLeft i) (n04PositiveRight i) κφ κX M H :=
    hbound z.1 z.2.1 z.2.2
  have href (side : Bool) (θ : ℝ) :
      F z₀ side =ᶠ[𝓝 (if side then n04PositiveRight i else n04PositiveLeft i, θ)]
          (id : PolarPoint → PolarPoint) ∧
      q z₀ side =ᶠ[𝓝 (if side then n04PositiveRight i else n04PositiveLeft i, θ)]
          (fun _ => (1 : ℝ)) :=
    n04Coordinates_positiveSource_reference_germs hT hS hN hfield e (j side) θ
  have hout := exists_wholePositiveTransport_family (F := F) (q := q) (a := a) (b := b)
    (l := n04PositiveLeft i) (r := n04PositiveRight i) z₀ n
    hlc hcd hdr hκφ hκφone hκX hM hH hdata
    (fun z => (hfinite z).angular_lower) (fun z => (hfinite z).radial_lower)
    (fun z => (hfinite z).coordinate_jets) (fun z => (hfinite z).height_value)
    (fun z => (hfinite z).height_inverse) (fun z => (hfinite z).height_jets) href
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
