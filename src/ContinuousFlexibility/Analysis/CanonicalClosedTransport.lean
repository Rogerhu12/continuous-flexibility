import ContinuousFlexibility.Analysis.CanonicalClosedInverseJets

/-!
# Actual reference-to-current transport at physical boundaries

The full boundary inverse germs in the canonical geometry give ordinary
smoothness of the stored transition at every reference closed-piece point.
The height ratio is positive and smooth there as well. These are local
consequences for the actual maps, before any global gluing or estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

def n04CoordinatesCurrentHeightRatio {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : ℝ :=
  K.height (C.referenceState, 0) m p /
    K.height z m (canonicalCurrentPoint C K z m p)

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}
  (hA : CanonicalGeometry D S C K base ε)
  (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
  (hs₀ : stateSector S C.referenceState)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ)

theorem n04Coordinates_referenceClosed_eq_interval :
    physicalPieceClosed S K (C.referenceState, 0) m =
      Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ (univ : Set ℝ) := by
  change closure (physicalPieceOpen S K (C.referenceState, 0) m) = _
  rw [hA.referenceDomain m, referencePhysicalPieceOpen, closure_prod_eq,
    closure_Ioo (hA.referenceBounds m).1.ne, closure_univ]

include hA hz₀ hs₀ hz hs

theorem n04Coordinates_currentPoint_mapsTo_closed :
    MapsTo (canonicalCurrentPoint C K z m)
      (physicalPieceClosed S K (C.referenceState, 0) m)
      (physicalPieceClosed S K z m) := by
  intro p hp
  exact (hA.boundary z hz hs m).2.1
    ((hA.boundary _ hz₀ hs₀ m).1 hp)

theorem n04Coordinates_currentPoint_contDiffAt_closed
    {p : PolarPoint} (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m) :
    ContDiffAt ℝ ∞ (canonicalCurrentPoint C K z m) p := by
  have hclosed := hA.boundary _ hz₀ hs₀ m
  exact (n04b_inverseChart_contDiffAt_closed hA hz hs m (hclosed.1 hp)).comp p
    (hclosed.2.2.2.2.1 p hp).1

theorem n04Coordinates_currentHeightRatio_contDiffAt_pos_closed
    {p : PolarPoint} (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m) :
    ContDiffAt ℝ ∞ (n04CoordinatesCurrentHeightRatio C K z m) p ∧
      0 < n04CoordinatesCurrentHeightRatio C K z m p := by
  have hx := n04Coordinates_currentPoint_mapsTo_closed hA hz₀ hs₀ hz hs m hp
  have href := (hA.boundary _ hz₀ hs₀ m).2.2.2.2.1 p hp
  have hcur := (hA.boundary z hz hs m).2.2.2.2.1 _ hx
  have hτ := n04Coordinates_currentPoint_contDiffAt_closed hA hz₀ hs₀ hz hs m hp
  exact ⟨href.2.1.div (hcur.2.1.comp p hτ) hcur.2.2.2.ne',
    div_pos href.2.2.2 hcur.2.2.2⟩

theorem n04Coordinates_referencePoint_currentPoint_germ
    {p : PolarPoint} (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m) :
    canonicalReferencePoint C K z m ∘ canonicalCurrentPoint C K z m =ᶠ[𝓝 p]
      (id : PolarPoint → PolarPoint) := by
  have hclosed := hA.boundary _ hz₀ hs₀ m
  have hq := hclosed.1 hp
  have hF := (hclosed.2.2.2.2.1 p hp).1.continuousAt
  have hcurrent := (canonicalClosed_inverse_germs hA hz hs m hq).2.comp_tendsto hF
  have hreference : K.inverseChart (C.referenceState, 0) m ∘
      K.chart (C.referenceState, 0) m =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) := by
    simpa only [hclosed.2.2.1 p hp] using
      (canonicalClosed_inverse_germs hA hz₀ hs₀ m hq).1
  filter_upwards [hcurrent, hreference] with x hx hr
  change K.chart z m (K.inverseChart z m (K.chart (C.referenceState, 0) m x)) =
    K.chart (C.referenceState, 0) m x at hx
  change K.inverseChart (C.referenceState, 0) m
    (K.chart z m (K.inverseChart z m (K.chart (C.referenceState, 0) m x))) = x
  rw [hx]
  exact hr

end ContinuousFlexibility.Analysis
