import ContinuousFlexibility.Analysis.WholePositiveEndpointFields

/-!
# Actual reference-state identity germs

Closed inverse identities imply that the stored reference-to-reference
map is the identity on a true neighborhood of each physical root point.
The positive reference height is nonzero on a neighborhood, so the
corresponding actual ratio equals one there. Certified ambient sources
satisfy the same assertions directly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem canonicalCurrentPoint_reference_fields_germs
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState) (k : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) k) :
    canonicalCurrentPoint C K (C.referenceState, 0) k =ᶠ[𝓝 p]
        (id : PolarPoint → PolarPoint) ∧
      n04CoordinatesCurrentHeightRatio C K (C.referenceState, 0) k =ᶠ[𝓝 p]
        (fun _ => (1 : ℝ)) := by
  have hclosed := hA.boundary _ hz₀ hs₀ k
  have hq := hclosed.1 hp
  have hτ : K.inverseChart (C.referenceState, 0) k ∘
      K.chart (C.referenceState, 0) k =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) := by
    simpa only [hclosed.2.2.1 p hp] using
      (canonicalClosed_inverse_germs hA hz₀ hs₀ k hq).1
  have hheight := hclosed.2.2.2.2.1 p hp
  have hpositive : ∀ᶠ x in 𝓝 p, 0 < K.height (C.referenceState, 0) k x :=
    continuousAt_const.eventually_lt hheight.2.1.continuousAt hheight.2.2.2
  refine ⟨hτ, ?_⟩
  filter_upwards [hτ, hpositive] with x hx hpos
  change canonicalCurrentPoint C K (C.referenceState, 0) k x = x at hx
  change K.height (C.referenceState, 0) k x /
      K.height (C.referenceState, 0) k
        (canonicalCurrentPoint C K (C.referenceState, 0) k x) = 1
  rw [hx, div_self hpos.ne']

theorem n04Coordinates_positiveSource_reference_germs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    n04PositiveSourceMap j K (C.referenceState, 0) =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)]
        (id : PolarPoint → PolarPoint) ∧
      n04PositiveSourceHeight j K (C.referenceState, 0)
        =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)] (fun _ => (1 : ℝ)) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hA : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hcut : CanonicalCutGeometry S C K base ε :=
    n04bActualTypedAtlas_cutGeometry hT hS hN hfield e
  have hz₀ := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ := hN.1.1.2.2.1.stateSector
  rcases j with ⟨o, ho⟩
  cases o with
  | none => exact ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
  | some m =>
      change n04PositiveEndpoint i side = (if side then C.left m else C.right m) at ho
      change
        canonicalCurrentPoint C K (C.referenceState, 0)
            (if side then (K.cutPair m).1 else (K.cutPair m).2)
          =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)] (id : PolarPoint → PolarPoint) ∧
        n04CoordinatesCurrentHeightRatio C K (C.referenceState, 0)
            (if side then (K.cutPair m).1 else (K.cutPair m).2)
          =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)] (fun _ => (1 : ℝ))
      rw [ho]
      have hp := (canonicalCutRoot_mem_closed_and_zero hA hcut hz₀ hs₀ m (!side) θ).1
      have hg := canonicalCurrentPoint_reference_fields_germs hA hz₀ hs₀
        (if !side then (K.cutPair m).2 else (K.cutPair m).1) hp
      cases side <;> exact hg

end ContinuousFlexibility.Analysis

