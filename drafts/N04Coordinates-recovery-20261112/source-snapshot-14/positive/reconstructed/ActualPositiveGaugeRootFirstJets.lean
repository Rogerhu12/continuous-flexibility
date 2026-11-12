import ContinuousFlexibility.Analysis.ActualPositiveReferenceFirstJets
import ContinuousFlexibility.Analysis.WholePositiveActualRootFirstJets

/-!
# Current root first jets of the actual fixed positive reference gauge

The same reference interpolation and the same positive transport family
are used throughout. The reference scalar jets are the actual factory
outputs, while the relative jets come from its certified endpoint
matching. The true negative inverse supplies the reference angle of
each current root point, so no angular reparametrization is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04Coordinates_actual_positive_gauge_root_firstJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss n : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (i : N04PositiveComponent D.a D.b (deriv D.w))
    (j : ∀ side, N04PositiveEndpointSource C i side) {Y H : ℝ → ℝ}
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hYjets : ∀ side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => Y p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceCoordinate (j side)
          (n04bActualTypedAtlas hT hS hN hfield e)) (n04PositiveEndpoint i side, θ))
    (hHjets : ∀ side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => H p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceHeight (j side)
          (n04bActualTypedAtlas hT hS hN hfield e)) (n04PositiveEndpoint i side, θ))
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (hn : 1 ≤ n)
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {c d J Hbound : ℝ}
    (hm : WholePositiveTransportMatching n
      (fun side => n04PositiveSourceMap (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
      (fun side => n04PositiveSourceHeight (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
      τ σ Q (n04PositiveLeft i) (n04PositiveRight i) c d J Hbound)
    (m : ℕ) (side : Bool)
    (hadj : n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := if side then (K.cutPair m).2 else (K.cutPair m).1
    let r := if side then C.right m else C.left m
    let v : ℝ := if !side then 1 else 0
    let s : ℝ := if !side then 1 else -1
    let A : PolarPoint → PolarPoint := fun p => (p.1 - v, p.2)
    let B : PolarPoint → PolarPoint := fun p => (s * p.1, p.2)
    ∀ θ, (A (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ
        (r, θ))).1 = 0 ∧
      FiniteFullJetMatch 1 (r, θ)
        (A ∘ wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ)
        (B ∘ K.chart z k) ∧
      FiniteFullJetMatch 1 (r, θ)
        (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => H p.1) σ Q)
        (K.height z k) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hA : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hcut : CanonicalCutGeometry S C K base ε :=
    n04bActualTypedAtlas_cutGeometry hT hS hN hfield e
  have hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ : stateSector S C.referenceState := hN.1.1.2.2.1.stateSector
  have hrelative := wholePositiveTransportMatching_actual_root_firstJets
    hN.1.1 hA hcut hz₀ hs₀ hz hs hn j hm m side hadj
  have href := n04Coordinates_actual_positive_reference_firstJets
    hT hS hN hfield e i j hgeometry hYjets hHjets m side hadj
  let s : ℝ := if !side then 1 else -1
  have hB : ContDiff ℝ ∞ (fun p : PolarPoint => (s * p.1, p.2)) :=
    (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  exact canonicalReferenceGauge_rootCircle_firstJets hA hcut hz₀ hs₀ hz hs m side
    hm.geometry.inverse_smooth hm.geometry.left_inverse hB
    (fun θ => (hrelative θ).1) (fun θ => (hrelative θ).2)
    (fun θ => (href θ).2.1) (fun θ => (href θ).2.2) (fun θ => (href θ).1)

end ContinuousFlexibility.Analysis
