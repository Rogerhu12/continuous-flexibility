import ContinuousFlexibility.Analysis.ActualPositiveGaugeRootFirstJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData

/-!
# Actual root first jets in the new whole-atlas record

The reference cylinder and height and the relative family are the same
objects used by the displayed atlas constructor. Its positive and
negative field identities therefore turn the proved raw first jets
into first jets of the record's endpoint-aligned charts and heights.
No new endpoint, orientation, map, or state is selected here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04WholeReferenceGaugeAtlasData_actual_root_firstJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss n : ℕ} {ε : ℝ}
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
    (N : Set ℝ) (i : N04PositiveComponent D.a D.b (deriv D.w))
    (j : ∀ side, N04PositiveEndpointSource C i side)
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hYjets : ∀ side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => Y i p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceCoordinate (j side)
          (n04bActualTypedAtlas hT hS hN hfield e₀)) (n04PositiveEndpoint i side, θ))
    (hHjets : ∀ side θ a, a ≤ 1 →
      iteratedFDeriv ℝ a (fun p : PolarPoint => H i p.1)
          (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ a (n04PositiveReferenceSourceHeight (j side)
          (n04bActualTypedAtlas hT hS hN hfield e₀)) (n04PositiveEndpoint i side, θ))
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (hn : 1 ≤ n) {c d J Hbound : ℝ}
    (hm : WholePositiveTransportMatching n
      (fun side => n04PositiveSourceMap (j side) (n04bActualTypedAtlas hT hS hN hfield e₀) z)
      (fun side => n04PositiveSourceHeight (j side) (n04bActualTypedAtlas hT hS hN hfield e₀) z)
      (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i) c d J Hbound)
    (ip ineg m : ℕ) (side : Bool) (hip : e ip = .inr i)
    (hineg : e ineg = .inl (m, side))
    (hadj : n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell
      (fun i => positiveReferenceCylinderChart (Y i))
      (fun i => positiveReferenceCylinderInverse (Y i))
      (fun i p => H i p.1) τ σ Q N
    let r := if side then C.right m else C.left m
    let v : ℝ := if !side then 1 else 0
    let s : ℝ := if !side then 1 else -1
    ∀ θ, (CanonicalGeometry.endpointAlignedChart V z ip v 1 (r, θ)).1 = 0 ∧
      FiniteFullJetMatch 1 (r, θ)
        (CanonicalGeometry.endpointAlignedChart V z ip v 1)
        (CanonicalGeometry.endpointAlignedChart V z ineg 0 s) ∧
      FiniteFullJetMatch 1 (r, θ) (V.height z ip) (V.height z ineg) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let ψ := fun i => positiveReferenceCylinderChart (Y i)
  let χ := fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ := fun i (p : PolarPoint) => H i p.1
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let k := if side then (K.cutPair m).2 else (K.cutPair m).1
  let v : ℝ := if !side then 1 else 0
  let s : ℝ := if !side then 1 else -1
  obtain ⟨_, _, _, _, _, _, _, hFp, _, hhp, _, _⟩ :=
    n04WholeReferenceGaugeAtlasData_positive_fields
      C L K e cell ψ χ h₀ τ σ Q N z ip i hip
  obtain ⟨_, _, _, _, _, _, _, hFn, _, hhn, _, _⟩ :=
    n04WholeReferenceGaugeAtlasData_negative_fields
      C L K e cell ψ χ h₀ τ σ Q N z ineg (m, side) hineg
  have hpositive : CanonicalGeometry.endpointAlignedChart V z ip v 1 =
      (fun p : PolarPoint => (p.1 - v, p.2)) ∘
        wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart (Y i)) (σ z i) := by
    funext p
    simp only [CanonicalGeometry.endpointAlignedChart, V, hFp, ψ, one_mul, Function.comp_apply]
  have hnegative : CanonicalGeometry.endpointAlignedChart V z ineg 0 s =
      (fun p : PolarPoint => (s * p.1, p.2)) ∘ K.chart z k := by
    funext p
    simp only [CanonicalGeometry.endpointAlignedChart, V, hFn, k, sub_zero, Function.comp_apply]
  have hraw := n04Coordinates_actual_positive_gauge_root_firstJets
    hT hS hN hfield e₀ i j hgeometry hYjets hHjets hz hs hn hm m side hadj
  dsimp only
  intro θ
  rw [hpositive, hnegative, hhp, hhn]
  exact hraw θ

end ContinuousFlexibility.Analysis
