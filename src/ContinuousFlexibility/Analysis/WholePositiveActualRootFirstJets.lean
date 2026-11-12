import ContinuousFlexibility.Analysis.CanonicalWholePositiveRootMatching
import ContinuousFlexibility.Analysis.CanonicalReferenceGaugeRootCircleJets

/-!
# The selected positive family's actual negative root first jets

The certified source at an adjacent interior endpoint is the same
negative component. Its displayed map and height therefore agree with
the original stored half, and the already constructed finite matching
gives first jets directly against that half. The original N01 witness
and a possibly restricted atlas neighborhood are kept separate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem wholePositiveTransportMatching_actual_root_firstJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {originalBase originalLoss base n : ℕ} {originalRadius ε : ℝ}
    (hN : N01Properties D T S C originalBase originalLoss originalRadius)
    (hA : CanonicalGeometry D S C K base ε)
    (hcut : CanonicalCutGeometry S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (hn : 1 ≤ n)
    {i : N04PositiveComponent D.a D.b (deriv D.w)}
    (j : ∀ side, N04PositiveEndpointSource C i side)
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {c d J H : ℝ}
    (hm : WholePositiveTransportMatching n
      (fun side => n04PositiveSourceMap (j side) K z)
      (fun side => n04PositiveSourceHeight (j side) K z)
      τ σ Q (n04PositiveLeft i) (n04PositiveRight i) c d J H)
    (m : ℕ) (side : Bool)
    (hadj : n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m)) :
    let k := if side then (K.cutPair m).2 else (K.cutPair m).1
    let r := if side then C.right m else C.left m
    ∀ θ, FiniteFullJetMatch 1 (r, θ) τ (canonicalCurrentPoint C K z k) ∧
      FiniteFullJetMatch 1 (r, θ) Q (n04CoordinatesCurrentHeightRatio C K z k) := by
  have hroot : n04PositiveEndpoint i (!side) =
      (if !side then C.left m else C.right m) := by
    cases side <;> exact hadj
  have hj := n04PositiveEndpointSource_eq_some_of_negative_endpoint hN (j (!side)) m hroot
  have hsource :
      n04PositiveSourceMap (j (!side)) K z =
        canonicalCurrentPoint C K z (if side then (K.cutPair m).2 else (K.cutPair m).1) ∧
      n04PositiveSourceHeight (j (!side)) K z =
        n04CoordinatesCurrentHeightRatio C K z
          (if side then (K.cutPair m).2 else (K.cutPair m).1) := by
    simp only [n04PositiveSourceMap, n04PositiveSourceHeight, hj]
    cases side <;> exact ⟨rfl, rfl⟩
  dsimp only
  intro θ
  let k := if side then (K.cutPair m).2 else (K.cutPair m).1
  have hp := (canonicalCutRoot_mem_closed_and_zero hA hcut hz₀ hs₀ m side θ).1
  refine ⟨⟨hm.geometry.smooth.contDiffAt,
    n04Coordinates_currentPoint_contDiffAt_closed hA hz₀ hs₀ hz hs k hp, ?_⟩,
    ⟨hm.height_smooth.contDiffAt,
    (n04Coordinates_currentHeightRatio_contDiffAt_pos_closed hA hz₀ hs₀ hz hs k hp).1, ?_⟩⟩
  · intro a ha
    have hjet := hm.coordinate_jets (!side) a (by omega) θ
    change iteratedFDeriv ℝ a τ (n04PositiveEndpoint i (!side), θ) =
      iteratedFDeriv ℝ a (n04PositiveSourceMap (j (!side)) K z)
        (n04PositiveEndpoint i (!side), θ) at hjet
    rw [hadj, hsource.1] at hjet
    exact hjet
  · intro a ha
    have hjet := hm.height_jets (!side) a (ha.trans hn) θ
    change iteratedFDeriv ℝ a Q (n04PositiveEndpoint i (!side), θ) =
      iteratedFDeriv ℝ a (n04PositiveSourceHeight (j (!side)) K z)
        (n04PositiveEndpoint i (!side), θ) at hjet
    rw [hadj, hsource.2] at hjet
    exact hjet

end ContinuousFlexibility.Analysis
