import ContinuousFlexibility.Analysis.CanonicalActualEndpointFields
import ContinuousFlexibility.Analysis.WholePositiveReferenceGaugeFirstJets

/-!
# The stored closed atlas fields in the reference gauge

At a reference closed-piece point, the actual reference-to-current map
and its actual inverse reconstruct the stored current chart and height
on a full ordinary neighborhood. This identifies the negative-side
terms of the first-jet transfer without assuming a raw matching target.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hA : CanonicalGeometry D S C K base ε)
  (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
  (hs₀ : stateSector S C.referenceState)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
  (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m)

include hA hz₀ hs₀ hz hs hp

theorem canonicalReferenceGauge_reconstructs_closed_fields :
    (wholePositiveReferenceGaugeChart (K.chart (C.referenceState, 0) m)
        (canonicalReferencePoint C K z m)
      =ᶠ[𝓝 (canonicalCurrentPoint C K z m p)] K.chart z m) ∧
    (wholePositiveReferenceGaugeHeight (K.height (C.referenceState, 0) m)
        (canonicalReferencePoint C K z m) (n04CoordinatesCurrentHeightRatio C K z m)
      =ᶠ[𝓝 (canonicalCurrentPoint C K z m p)] K.height z m) := by
  let x := canonicalCurrentPoint C K z m p
  have hclosed₀ := hA.boundary _ hz₀ hs₀ m
  have hclosed := hA.boundary z hz hs m
  have hq := hclosed₀.1 hp
  have hx : x ∈ physicalPieceClosed S K z m :=
    n04Coordinates_currentPoint_mapsTo_closed hA hz₀ hs₀ hz hs m hp
  have hcur := hclosed.2.2.2.2.1 x hx
  have href := hclosed₀.2.2.2.2.1 p hp
  have hFx : K.chart z m x = K.chart (C.referenceState, 0) m p :=
    hclosed.2.2.2.1 _ hq
  have hFto : Tendsto (K.chart z m) (𝓝 x)
      (𝓝 (K.chart (C.referenceState, 0) m p)) := by
    rw [← hFx]
    exact hcur.1.continuousAt.tendsto
  have hreference := (canonicalClosed_inverse_germs hA hz₀ hs₀ m hq).2
  have hinv := canonicalCurrentPoint_closed_inverse_data hA hz₀ hs₀ hz hs m hp
  have hSp : canonicalReferencePoint C K z m x = p := hinv.2.1.eq_of_nhds
  have hSto : Tendsto (canonicalReferencePoint C K z m) (𝓝 x) (𝓝 p) := by
    simpa only [hSp] using hinv.1.continuousAt.tendsto
  have hrefpos : ∀ᶠ y in 𝓝 p, 0 < K.height (C.referenceState, 0) m y :=
    href.2.1.continuousAt.tendsto.eventually (Ioi_mem_nhds href.2.2.2)
  have hcurpos : ∀ᶠ y in 𝓝 x, 0 < K.height z m y :=
    hcur.2.1.continuousAt.tendsto.eventually (Ioi_mem_nhds hcur.2.2.2)
  constructor
  · filter_upwards [hreference.comp_tendsto hFto] with y hy
    exact hy
  · filter_upwards [hinv.2.2, hSto.eventually hrefpos, hcurpos] with y hy h₀y hzy
    change canonicalCurrentPoint C K z m (canonicalReferencePoint C K z m y) = y at hy
    rw [wholePositiveReferenceGaugeHeight_eq, n04CoordinatesCurrentHeightRatio, hy]
    field_simp [h₀y.ne', hzy.ne']
    <;> ring

/-- Every finite ordinary jet of the reconstructed negative fields is
the jet of the same stored current field, at the same actual image. -/
theorem canonicalReferenceGauge_closed_fullJets (n : ℕ) :
    FiniteFullJetMatch n (canonicalCurrentPoint C K z m p)
        (wholePositiveReferenceGaugeChart (K.chart (C.referenceState, 0) m)
          (canonicalReferencePoint C K z m)) (K.chart z m) ∧
      FiniteFullJetMatch n (canonicalCurrentPoint C K z m p)
        (wholePositiveReferenceGaugeHeight (K.height (C.referenceState, 0) m)
          (canonicalReferencePoint C K z m) (n04CoordinatesCurrentHeightRatio C K z m))
        (K.height z m) := by
  let x := canonicalCurrentPoint C K z m p
  have hx : x ∈ physicalPieceClosed S K z m :=
    n04Coordinates_currentPoint_mapsTo_closed hA hz₀ hs₀ hz hs m hp
  have hcur := (hA.boundary z hz hs m).2.2.2.2.1 x hx
  have href := (hA.boundary _ hz₀ hs₀ m).2.2.2.2.1 p hp
  have hinv := canonicalCurrentPoint_closed_inverse_data hA hz₀ hs₀ hz hs m hp
  have hSp : canonicalReferencePoint C K z m x = p := hinv.2.1.eq_of_nhds
  have hFref : ContDiffAt ℝ ∞ (K.chart (C.referenceState, 0) m)
      (canonicalReferencePoint C K z m x) := by
    rw [hSp]
    exact href.1
  have hquot : ContDiffAt ℝ ∞
      (fun y => K.height (C.referenceState, 0) m y /
        n04CoordinatesCurrentHeightRatio C K z m y)
      (canonicalReferencePoint C K z m x) := by
    rw [hSp]
    have hQ := n04Coordinates_currentHeightRatio_contDiffAt_pos_closed
      hA hz₀ hs₀ hz hs m hp
    exact href.2.1.div hQ.1 hQ.2.ne'
  have hheight : ContDiffAt ℝ ∞
      (wholePositiveReferenceGaugeHeight (K.height (C.referenceState, 0) m)
        (canonicalReferencePoint C K z m) (n04CoordinatesCurrentHeightRatio C K z m)) x := by
    simpa only [wholePositiveReferenceGaugeHeight, wholePositiveChartHeight,
      Function.comp_def, div_eq_mul_inv] using hquot.comp x hinv.1
  have he := canonicalReferenceGauge_reconstructs_closed_fields hA hz₀ hs₀ hz hs m hp
  exact ⟨finiteFullJetMatch_of_germ (hFref.comp x hinv.1) hcur.1 he.1,
    finiteFullJetMatch_of_germ hheight hcur.2.1 he.2⟩

end ContinuousFlexibility.Analysis
