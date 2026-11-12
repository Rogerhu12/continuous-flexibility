import ContinuousFlexibility.Analysis.N04RealizationLogHeightTraceRegularity
import ContinuousFlexibility.Analysis.WholePositiveEndpointFields

/-!
# Logarithmic Taylor traces of the retained actual positive sources

The endpoint sources and the actual typed atlas are supplied once. Their
proved root smoothness and positivity construct the logarithmic traces
from the raw height-axis towers. The finite input degree may be three;
neither a new source nor a smaller parameter domain is chosen here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The existing positive Taylor data use the logarithm of the actual
source height. Raw axis towers through the same finite degree suffice. -/
def n04Realization_actualPositive_logTrace_parameterTower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {U : Set X} (hU : IsOpen U) (z : X → AnnularState S × ℝ)
    (hz : ∀ x ∈ U, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x ∈ U, stateSector S (z x).1)
    (i : N04PositiveComponent D.a D.b (deriv D.w))
    (src : ∀ side, N04PositiveEndpointSource C i side) (n : ℕ)
    (J : ∀ side, ∀ j : ℕ, j ≤ n → ∀ b θ,
      SmoothDirections U (fun x => iteratedDeriv b
        (radialBoundaryJet
          (n04PositiveSourceHeight (src side) (n04bActualTypedAtlas hT hS hN hfield e) (z x))
          (n04PositiveEndpoint i side) j) θ))
    (side : Bool) (j : ℕ) (hj : j ≤ n) (b : ℕ) (θ : ℝ) :
    SmoothDirections U (fun x => iteratedDeriv b
      (positiveHeightTaylorData (n04PositiveLeft i) (n04PositiveRight i) (fun _ => 1)
        (fun side => n04PositiveSourceHeight (src side)
          (n04bActualTypedAtlas hT hS hN hfield e) (z x)) side j) θ) := by
  let K : CanonicalData S := n04bActualTypedAtlas hT hS hN hfield e
  let f : X → PolarPoint → ℝ := fun x => n04PositiveSourceHeight (src side) K (z x)
  have hroot (x : X) (hx : x ∈ U) (η : ℝ) :
      ContDiffAt ℝ ∞ (f x) (n04PositiveEndpoint i side, η) ∧
        0 < f x (n04PositiveEndpoint i side, η) :=
    (n04Coordinates_actualAtlas_positiveEndpoint_of_source
      hT hS hN hfield e (src side) (hz x hx) (hs x hx)).height_root η
  let JT := n04Realization_logBoundaryTrace_parameterTower hU
    (n04PositiveEndpoint i side) j
    (fun x hx η => (hroot x hx η).1) (fun x hx η => (hroot x hx η).2)
    (fun d hd => J side d (hd.trans hj)) b θ
  have hlog (x : X) : (fun p => Real.log (f x p)) =
      boundaryHeightLogRatio (fun _ => 1)
        (n04PositiveSourceHeight (src side) (n04bActualTypedAtlas hT hS hN hfield e) (z x)) := by
    funext p
    simp only [boundaryHeightLogRatio, div_one, f, K]
  exact JT.congr (fun x _ => by
    rw [positiveHeightTaylorData, ← hlog x]
    rfl)

/-- An ambient endpoint has the actual unit source, hence every
logarithmic Taylor coefficient and every angular derivative vanish. -/
theorem n04Realization_positiveSource_logTrace_none
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {i : N04PositiveComponent D.a D.b (deriv D.w)}
    (src : ∀ side, N04PositiveEndpointSource C i side)
    (K : CanonicalData S) (z : AnnularState S × ℝ)
    (side : Bool) (hside : (src side).val = none) (j b : ℕ) (θ : ℝ) :
    iteratedDeriv b
      (positiveHeightTaylorData (n04PositiveLeft i) (n04PositiveRight i) (fun _ => 1)
        (fun side => n04PositiveSourceHeight (src side) K z) side j) θ = 0 := by
  have hlog : boundaryHeightLogRatio (fun _ => 1) (fun _ => 1) =
      (fun _ : PolarPoint => (0 : ℝ)) := by
    funext p
    simp only [boundaryHeightLogRatio, div_one, Real.log_one]
  have hzero : positiveHeightTaylorData (n04PositiveLeft i) (n04PositiveRight i)
      (fun _ => 1) (fun side => n04PositiveSourceHeight (src side) K z) side j =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext η
    simp only [positiveHeightTaylorData, n04PositiveSourceHeight, hside,
      hlog, radialBoundaryJet, iteratedDeriv_fun_const_zero]
  rw [hzero, iteratedDeriv_fun_const_zero]

end ContinuousFlexibility.Analysis
