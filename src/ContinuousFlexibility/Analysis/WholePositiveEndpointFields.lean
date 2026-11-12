import ContinuousFlexibility.Analysis.PositiveComponentAdjacency
import ContinuousFlexibility.Analysis.CanonicalActualEndpointFields

/-!
# State-independent endpoint sources for a whole positive component

Each endpoint source is chosen once from the actual reference partition.
An interior endpoint uses the opposite end of its genuine negative
neighbor. An ambient endpoint uses the identity and height one. The
resulting fields for every permitted state are the actual stored fields,
and their one-sided smoothness and symmetries are proved by the atlas
factory. No endpoint derivative estimate is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def N04PositiveEndpointSource {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (side : Bool) : Type :=
  {o : Option ℕ // match o with
    | none => n04PositiveEndpoint i side = (if side then D.b else D.a)
    | some m => n04PositiveEndpoint i side = (if side then C.left m else C.right m)}

def n04PositiveEndpointSource {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hD : RadialProfileGeometry D)
    (hC : controlGeometryConditions D S C)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (side : Bool) :
    N04PositiveEndpointSource C i side := by
  classical
  by_cases h : n04PositiveEndpoint i side = (if side then D.b else D.a)
  · exact ⟨none, h⟩
  · exact ⟨some (Classical.choose (n04PositiveEndpoint_exists_negative_neighbor hD hC i side h)),
      Classical.choose_spec (n04PositiveEndpoint_exists_negative_neighbor hD hC i side h)⟩

def n04PositiveSourceLeft {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {i : N04PositiveComponent D.a D.b (deriv D.w)}
    {side : Bool} (j : N04PositiveEndpointSource C i side) : ℝ :=
  match j.val with
  | none => n04PositiveLeft i
  | some m => C.left m

def n04PositiveSourceRight {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {i : N04PositiveComponent D.a D.b (deriv D.w)}
    {side : Bool} (j : N04PositiveEndpointSource C i side) : ℝ :=
  match j.val with
  | none => n04PositiveRight i
  | some m => C.right m

def n04PositiveSourceMap {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {i : N04PositiveComponent D.a D.b (deriv D.w)}
    {side : Bool} (j : N04PositiveEndpointSource C i side)
    (K : CanonicalData S) (z : AnnularState S × ℝ) : PolarPoint → PolarPoint :=
  match j.val with
  | none => id
  | some m => canonicalCurrentPoint C K z (if side then (K.cutPair m).1 else (K.cutPair m).2)

def n04PositiveSourceHeight {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {i : N04PositiveComponent D.a D.b (deriv D.w)}
    {side : Bool} (j : N04PositiveEndpointSource C i side)
    (K : CanonicalData S) (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  match j.val with
  | none => fun _ => 1
  | some m => n04CoordinatesCurrentHeightRatio C K z
      (if side then (K.cutPair m).1 else (K.cutPair m).2)

theorem n04Coordinates_actualAtlas_positiveEndpoint_of_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    OneSidedTransportEndpoint (n04PositiveSourceMap j K z)
      (n04PositiveSourceHeight j K z) (n04PositiveSourceLeft j)
      (n04PositiveSourceRight j) (n04PositiveEndpoint i side) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  rcases j with ⟨o, ho⟩
  cases o with
  | none =>
      have hD := n04b_profileGeometry_of_through03 hN
      have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
      have hb := (n04PositiveComponent_bounds hf i).2.1
      apply oneSidedTransportEndpoint_identity hb
      cases side
      · exact ⟨le_rfl, hb.le⟩
      · exact ⟨hb.le, le_rfl⟩
  | some m =>
      change OneSidedTransportEndpoint
        (canonicalCurrentPoint C K z (if side then (K.cutPair m).1 else (K.cutPair m).2))
        (n04CoordinatesCurrentHeightRatio C K z
          (if side then (K.cutPair m).1 else (K.cutPair m).2))
        (C.left m) (C.right m) (n04PositiveEndpoint i side)
      change n04PositiveEndpoint i side = (if side then C.left m else C.right m) at ho
      rw [ho]
      have ht := n04Coordinates_actualAtlas_endpoint_fields hT hS hN hfield e hz hs m (!side)
      cases side <;> exact ht

/-- The source choice precedes the state. Its absent-neighbor branch is
certified to be an ambient endpoint by the source subtype itself. -/
theorem n04Coordinates_exists_wholePositive_endpoint_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) :
    ∃ j : ∀ side, N04PositiveEndpointSource C i side,
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ side,
      let K := n04bActualTypedAtlas hT hS hN hfield e
      OneSidedTransportEndpoint (n04PositiveSourceMap (j side) K z)
        (n04PositiveSourceHeight (j side) K z) (n04PositiveSourceLeft (j side))
        (n04PositiveSourceRight (j side)) (n04PositiveEndpoint i side) := by
  let j : ∀ side, N04PositiveEndpointSource C i side :=
    n04PositiveEndpointSource (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1 i
  refine ⟨j, ?_⟩
  intro z hz hs side
  exact n04Coordinates_actualAtlas_positiveEndpoint_of_source hT hS hN hfield e (j side) hz hs

end ContinuousFlexibility.Analysis
