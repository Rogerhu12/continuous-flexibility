module

public import ContinuousFlexibility.Analysis.CanonicalReferenceGaugeReconstruction

/-!
# First jets against the same actual negative chart

Reference matching and the previously constructed relative first jets
give current raw chart and height matching. The old negative chart is
identified through its genuine closed inverse germs. The two fixed
normal alignments are common outer maps, so they introduce no change
to the selected transport, inverse, height, or evaluation point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem canonicalReferenceGauge_raw_firstJets
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m)
    {τ σ ψ A B : PolarPoint → PolarPoint} {h₀ Q : PolarPoint → ℝ}
    (hτ : FiniteFullJetMatch 1 p τ (canonicalCurrentPoint C K z m))
    (hσ : ContDiffAt ℝ ∞ σ (τ p))
    (hστ : σ ∘ τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint))
    (hQ : FiniteFullJetMatch 1 p Q (n04CoordinatesCurrentHeightRatio C K z m))
    (hψ : FiniteFullJetMatch 1 p (A ∘ ψ) (B ∘ K.chart (C.referenceState, 0) m))
    (hh₀ : FiniteFullJetMatch 1 p h₀ (K.height (C.referenceState, 0) m))
    (hB : ContDiff ℝ ∞ B) :
    FiniteFullJetMatch 1 (τ p)
        (A ∘ wholePositiveReferenceGaugeChart ψ σ) (B ∘ K.chart z m) ∧
      FiniteFullJetMatch 1 (τ p)
        (wholePositiveReferenceGaugeHeight h₀ σ Q) (K.height z m) := by
  have hinv := canonicalCurrentPoint_closed_inverse_data hA hz₀ hs₀ hz hs m hp
  have hS : ContDiffAt ℝ ∞ (canonicalReferencePoint C K z m) (τ p) := by
    rw [hτ.value]
    exact hinv.1
  have hright : canonicalCurrentPoint C K z m ∘ canonicalReferencePoint C K z m
      =ᶠ[𝓝 (τ p)] (id : PolarPoint → PolarPoint) := by
    rw [hτ.value]
    exact hinv.2.2
  have hQp : Q p ≠ 0 := by
    rw [hQ.value]
    exact (n04Coordinates_currentHeightRatio_contDiffAt_pos_closed
      hA hz₀ hs₀ hz hs m hp).2.ne'
  have hmatch := wholePositiveReferenceGauge_firstJets_of_transport
    hτ hσ hS hστ hinv.2.1 hright hψ hh₀ hQ hQp
  have hstored := canonicalReferenceGauge_closed_fullJets hA hz₀ hs₀ hz hs m hp 1
  have hstoredF : FiniteFullJetMatch 1 (τ p)
      (wholePositiveReferenceGaugeChart (K.chart (C.referenceState, 0) m)
        (canonicalReferencePoint C K z m)) (K.chart z m) := by
    rw [hτ.value]
    exact hstored.1
  have hstoredH : FiniteFullJetMatch 1 (τ p)
      (wholePositiveReferenceGaugeHeight (K.height (C.referenceState, 0) m)
        (canonicalReferencePoint C K z m) (n04CoordinatesCurrentHeightRatio C K z m))
      (K.height z m) := by
    rw [hτ.value]
    exact hstored.2
  exact ⟨hmatch.1.trans (hstoredF.comp hB.contDiffAt), hmatch.2.trans hstoredH⟩

/-- A zero normal reference value stays zero at the corresponding
current point; this uses the same inverse identity as the jet transfer. -/
theorem wholePositiveReferenceGaugeChart_normal_zero
    {p : PolarPoint} {τ σ ψ A : PolarPoint → PolarPoint}
    (hστ : σ (τ p) = p) (hzero : (A (ψ p)).1 = 0) :
    (A (wholePositiveReferenceGaugeChart ψ σ (τ p))).1 = 0 := by
  simpa only [wholePositiveReferenceGaugeChart, Function.comp_apply, hστ] using hzero

end ContinuousFlexibility.Analysis
