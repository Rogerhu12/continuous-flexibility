import ContinuousFlexibility.Analysis.CanonicalRootReferencePoint
import ContinuousFlexibility.Analysis.CanonicalReferenceGaugeFirstJetTransfer

/-!
# Raw first-jet matching at every actual current root point

The transfer is evaluated at the true negative reference point of the
current root point. The positive/negative relative jets and the fixed
reference data are all read at that same reference angle. This proves
the current-circle conclusion without an angular identification premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem canonicalReferenceGauge_rootCircle_firstJets
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hcut : CanonicalCutGeometry S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool)
    {τ σ ψ A B : PolarPoint → PolarPoint} {h₀ Q : PolarPoint → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hστ : Function.LeftInverse σ τ)
    (hB : ContDiff ℝ ∞ B) :
    let k := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    (∀ θ, FiniteFullJetMatch 1 (c, θ) τ (canonicalCurrentPoint C K z k)) →
    (∀ θ, FiniteFullJetMatch 1 (c, θ) Q (n04CoordinatesCurrentHeightRatio C K z k)) →
    (∀ θ, FiniteFullJetMatch 1 (c, θ) (A ∘ ψ)
      (B ∘ K.chart (C.referenceState, 0) k)) →
    (∀ θ, FiniteFullJetMatch 1 (c, θ) h₀ (K.height (C.referenceState, 0) k)) →
    (∀ θ, (A (ψ (c, θ))).1 = 0) →
    ∀ θ, (A (wholePositiveReferenceGaugeChart ψ σ (c, θ))).1 = 0 ∧
      FiniteFullJetMatch 1 (c, θ)
        (A ∘ wholePositiveReferenceGaugeChart ψ σ) (B ∘ K.chart z k) ∧
      FiniteFullJetMatch 1 (c, θ)
        (wholePositiveReferenceGaugeHeight h₀ σ Q) (K.height z k) := by
  dsimp only
  intro hτ hQ hψ hh₀ hzero θ
  let k := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  let q := canonicalReferencePoint C K z k (c, θ)
  have hq := canonicalReferencePoint_root_data hA hcut hz₀ hs₀ hz hs m side θ
  have hqeq : q = (c, q.2) := Prod.ext hq.1 rfl
  have hτq : FiniteFullJetMatch 1 q τ (canonicalCurrentPoint C K z k) := by
    rw [hqeq]
    exact hτ q.2
  have hQq : FiniteFullJetMatch 1 q Q (n04CoordinatesCurrentHeightRatio C K z k) := by
    rw [hqeq]
    exact hQ q.2
  have hψq : FiniteFullJetMatch 1 q (A ∘ ψ)
      (B ∘ K.chart (C.referenceState, 0) k) := by
    rw [hqeq]
    exact hψ q.2
  have hhq : FiniteFullJetMatch 1 q h₀ (K.height (C.referenceState, 0) k) := by
    rw [hqeq]
    exact hh₀ q.2
  have hτvalue : τ q = (c, θ) := hτq.value.trans hq.2.2
  have hjets := canonicalReferenceGauge_raw_firstJets hA hz₀ hs₀ hz hs k hq.2.1
    hτq hσ.contDiffAt (Filter.Eventually.of_forall hστ) hQq hψq hhq hB
  have hzq : (A (ψ q)).1 = 0 := by
    rw [hqeq]
    exact hzero q.2
  have hzcurrent := wholePositiveReferenceGaugeChart_normal_zero (hστ q) hzq
  rw [hτvalue] at hjets hzcurrent
  exact ⟨hzcurrent, hjets.1, hjets.2⟩

end ContinuousFlexibility.Analysis
