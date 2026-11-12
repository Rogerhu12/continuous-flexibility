import ContinuousFlexibility.Analysis.CanonicalWholePositiveTransport
import ContinuousFlexibility.Analysis.CanonicalWholeNegativeTransport
import ContinuousFlexibility.Analysis.WholeComponentFieldSelection

/-!
# Matching the constructed positive transport to the actual negative roots

A certified positive endpoint source cannot select a different negative
component at the same root: the true closed negative intervals are
disjoint. An ambient source cannot occur at an interior negative root.
This identifies the actual stored chart and height germ, and the finite
positive construction then matches its genuine negative neighbor.

The final constructor takes only the original finite endpoint bounds.
No root-matching or global-transport conclusion is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04PositiveEndpointSource_eq_some_of_negative_endpoint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) (m : ℕ)
    (hroot : n04PositiveEndpoint i side = (if side then C.left m else C.right m)) :
    j.val = some m := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  rcases j with ⟨o, ho⟩
  cases o with
  | none =>
      exfalso
      change n04PositiveEndpoint i side = (if side then D.b else D.a) at ho
      have he := hroot.symm.trans ho
      cases side
      · change C.right m = D.a at he
        exact ((hC.1 m).1.trans (hC.1 m).2.1).ne' he
      · change C.left m = D.b at he
        exact ((hC.1 m).2.1.trans (hC.1 m).2.2).ne he
  | some k =>
      change n04PositiveEndpoint i side = (if side then C.left k else C.right k) at ho
      have he := ho.symm.trans hroot
      have hk : (if side then C.left k else C.right k) ∈ Icc (C.left k) (C.right k) := by
        cases side
        · exact ⟨(hC.1 k).2.1.le, le_rfl⟩
        · exact ⟨le_rfl, (hC.1 k).2.1.le⟩
      have hm : (if side then C.left k else C.right k) ∈ Icc (C.left m) (C.right m) := by
        rw [he]
        cases side
        · exact ⟨(hC.1 m).2.1.le, le_rfl⟩
        · exact ⟨le_rfl, (hC.1 m).2.1.le⟩
      exact congrArg some (n04_negativeClosed_index_unique hN hk hm)

theorem n04PositiveSource_negative_root_germs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (K : CanonicalData S)
    (z : AnnularState S × ℝ)
    (i : N04PositiveComponent D.a D.b (deriv D.w))
    (j : ∀ side, N04PositiveEndpointSource C i side) (m : ℕ) (side : Bool)
    (hadj : n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m))
    (θ : ℝ) :
    (canonicalWholeNegativeTransport C K z m =ᶠ[𝓝 (if side then C.right m else C.left m, θ)]
      n04PositiveSourceMap (j (!side)) K z) ∧
    (canonicalWholeNegativeHeightRatio C K z m =ᶠ[𝓝 (if side then C.right m else C.left m, θ)]
      n04PositiveSourceHeight (j (!side)) K z) := by
  have hroot : n04PositiveEndpoint i (!side) =
      (if !side then C.left m else C.right m) := by
    cases side <;> exact hadj
  have hj := n04PositiveEndpointSource_eq_some_of_negative_endpoint hN (j (!side)) m hroot
  simp only [n04PositiveSourceMap, n04PositiveSourceHeight, hj]
  have hab : C.left m < C.right m := (hN.2.2.2.1.1 m).2.1
  have hτ := closedComponentField_root_germ
    (fun b => canonicalCurrentPoint C K z (if b then (K.cutPair m).2 else (K.cutPair m).1))
    hab side θ
  have hQ := closedComponentField_root_germ
    (fun b => n04CoordinatesCurrentHeightRatio C K z
      (if b then (K.cutPair m).2 else (K.cutPair m).1)) hab side θ
  cases side <;> exact ⟨hτ, hQ⟩

def WholePositiveNegativeRootJets
    {D : ReferenceData} {S : PhysicalSpacesData} (n : ℕ)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (i : N04PositiveComponent D.a D.b (deriv D.w))
    (τ : PolarPoint → PolarPoint) (Q : PolarPoint → ℝ) : Prop :=
  ∀ m side, n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m) →
    (∀ θ k, k ≤ n + 1 →
      iteratedFDeriv ℝ k (canonicalWholeNegativeTransport C K z m)
          (if side then C.right m else C.left m, θ) =
        iteratedFDeriv ℝ k τ (if side then C.right m else C.left m, θ)) ∧
    (∀ θ k, k ≤ n →
      iteratedFDeriv ℝ k (canonicalWholeNegativeHeightRatio C K z m)
          (if side then C.right m else C.left m, θ) =
        iteratedFDeriv ℝ k Q (if side then C.right m else C.left m, θ))

theorem wholePositiveTransportMatching_negative_root_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss n : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {K : CanonicalData S} {z : AnnularState S × ℝ}
    {i : N04PositiveComponent D.a D.b (deriv D.w)}
    (j : ∀ side, N04PositiveEndpointSource C i side)
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {c d J H : ℝ}
    (hm : WholePositiveTransportMatching n
      (fun side => n04PositiveSourceMap (j side) K z)
      (fun side => n04PositiveSourceHeight (j side) K z)
      τ σ Q (n04PositiveLeft i) (n04PositiveRight i) c d J H) :
    WholePositiveNegativeRootJets n C K z i τ Q := by
  intro m side hadj
  constructor
  · intro θ k hk
    have hjet := hm.coordinate_jets (!side) k hk θ
    change iteratedFDeriv ℝ k τ (n04PositiveEndpoint i (!side), θ) =
      iteratedFDeriv ℝ k (n04PositiveSourceMap (j (!side)) K z)
        (n04PositiveEndpoint i (!side), θ) at hjet
    rw [hadj] at hjet
    have hg := (n04PositiveSource_negative_root_germs hN K z i j m side hadj θ).1
    exact (hg.iteratedFDeriv ℝ k).eq_of_nhds.trans hjet.symm
  · intro θ k hk
    have hjet := hm.height_jets (!side) k hk θ
    change iteratedFDeriv ℝ k Q (n04PositiveEndpoint i (!side), θ) =
      iteratedFDeriv ℝ k (n04PositiveSourceHeight (j (!side)) K z)
        (n04PositiveEndpoint i (!side), θ) at hjet
    rw [hadj] at hjet
    have hg := (n04PositiveSource_negative_root_germs hN K z i j m side hadj θ).2
    exact (hg.iteratedFDeriv ℝ k).eq_of_nhds.trans hjet.symm

theorem n04Coordinates_wholePositive_transport_with_negative_root_jets
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
        (z = (C.referenceState, 0) → τ = id ∧ σ = id ∧ Q = (fun _ => (1 : ℝ))) ∧
        WholePositiveNegativeRootJets n C K z i τ Q := by
  have hout := n04Coordinates_wholePositive_transport_of_endpoint_bounds
    hT hS hN hfield e n i j hlc hcd hdr hκφ hκφone hκX hM hH hbound
  dsimp only at hout ⊢
  rcases hout with ⟨Clog, Mσ, δ, hClog, hMσ, hδ, hδρ, hδone, hrecip, hB, hout⟩
  refine ⟨Clog, Mσ, δ, hClog, hMσ, hδ, hδρ, hδone, hrecip, hB, ?_⟩
  intro z hz hs
  dsimp only
  have hzout := hout z hz hs
  exact ⟨hzout.1, hzout.2, wholePositiveTransportMatching_negative_root_jets hN.1.1 j hzout.1⟩

end ContinuousFlexibility.Analysis
