import ContinuousFlexibility.Analysis.CanonicalCutFirstJets
import ContinuousFlexibility.Analysis.AiryFirstJetMatching
import ContinuousFlexibility.Analysis.TwoOpenPieceGluing

/-!
# Genuine C¹ Airy first integrals on the whole negative component

The right travel coordinate is measured backwards from twice the cut
travel. The actual cut law proves equality of the values and full first
derivatives. The current-domain partition then gives C¹ gluing on the
entire negative component. This regularity theorem does not assert that
the stored physical coefficients already agree on the cut itself.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- One parameter treats both characteristic first integrals. -/
def canonicalGluedAiryIntegral (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (σ : ℝ) : PolarPoint → ℝ := by
  classical
  exact (physicalPieceOpen S K z (K.cutPair m).1).piecewise
    (airyFirstIntegral (K.chart z (K.cutPair m).1) σ)
    (fun p => airyFirstIntegral (K.chart z (K.cutPair m).2) (-σ) p +
      2 * σ * airyTravelPrimitive (K.cutRadius m))

/-- The common cut belongs to both genuine closed physical pieces, and
both forward charts have their prescribed common boundary value there. -/
theorem canonicalCut_closed_and_chart
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    canonicalCutPoint S K z m θ ∈ physicalPieceClosed S K z i ∧
      K.chart z i (canonicalCutPoint S K z m θ) = (K.cutRadius m, θ) := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  obtain ⟨_, _, _, _, _, hρ, hleft₀, hleft₁, hright₀, hright₁⟩ := hB.1.1 m
  have hleft : K.left i = 0 := by cases side <;> assumption
  have hright : K.right i = K.cutRadius m := by cases side <;> assumption
  have hq : (K.cutRadius m, θ) ∈ canonicalClosed S K i := by
    change (K.left i ≤ K.cutRadius m ∧ K.cutRadius m ≤ K.right i) ∧ True
    exact ⟨⟨by simpa only [hleft] using hρ.le, by rw [hright]⟩, trivial⟩
  have hpoint : K.inverseChart z i (K.cutRadius m, θ) = canonicalCutPoint S K z m θ := by
    cases side with
    | false => rfl
    | true => exact (hB.1.2 z hz hs m).1 θ
  have hclosed := hA.boundary z hz hs i
  exact ⟨hpoint ▸ hclosed.2.1 hq, by
    simpa only [hpoint] using hclosed.2.2.2.1 (K.cutRadius m, θ) hq⟩

/-- The whole component has an actual continuously differentiable first
integral. No hypothesis bounds the number of crossings of the cut. -/
theorem contDiffOn_canonicalGluedAiryIntegral
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (σ : ℝ) :
    ContDiffOn ℝ 1 (canonicalGluedAiryIntegral S K z m σ)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  classical
  let N : Set PolarPoint := Ioo (C.left m) (C.right m) ×ˢ univ
  let Γ : Set PolarPoint := Set.range (canonicalCutPoint S K z m)
  obtain ⟨_, _, _, _, _, hρ, hleft₀, hleft₁, _, _⟩ := hB.1.1 m
  obtain ⟨_, _, hdisjoint, hcover, _, _⟩ := hB.1.2 z hz hs m
  have hcut (side : Bool) (θ : ℝ) := canonicalCut_closed_and_chart hA hB hz hs m side θ
  have hΓ : Γ ⊆ closure (physicalPieceOpen S K z (K.cutPair m).1) ∩
      closure (physicalPieceOpen S K z (K.cutPair m).2) := by
    rintro p ⟨θ, rfl⟩
    exact ⟨(hcut false θ).1, (hcut true θ).1⟩
  have hregular (i j : ℕ) (hleft : K.left i = 0)
      (hdisj : Disjoint (physicalPieceOpen S K z i) (physicalPieceOpen S K z j))
      (hcov : physicalPieceOpen S K z i ∪ physicalPieceOpen S K z j = N \ Γ)
      (hvalue : ∀ θ, K.chart z i (canonicalCutPoint S K z m θ) = (K.cutRadius m, θ))
      (τ : ℝ) (p : PolarPoint) (hp : p ∈ N ∩ closure (physicalPieceOpen S K z i)) :
      ContDiffAt ℝ ∞ (airyFirstIntegral (K.chart z i) τ) p := by
    have hwhere := openPieces_closure_subset_piece_union_interface
      (hA.domains z hz hs j).1 hdisj hcov hp
    have hξ : 0 < (K.chart z i p).1 := by
      rcases hwhere with hopen | ⟨θ, rfl⟩
      · simpa only [hleft] using ((hA.charts z hz hs i).1 hopen).1.1
      · simpa only [hvalue θ] using hρ
    exact contDiffAt_airyFirstIntegral
      ((hA.boundary z hz hs i).2.2.2.2.1 p hp.2).1 hξ τ
  unfold canonicalGluedAiryIntegral
  apply contDiffOn_one_piecewise_two_open_domains
    (t := physicalPieceOpen S K z (K.cutPair m).2) (Γ := Γ)
    (isOpen_Ioo.prod isOpen_univ) (hA.domains z hz hs (K.cutPair m).1).1
    (hA.domains z hz hs (K.cutPair m).2).1 hdisjoint hcover hΓ
  · intro p hp
    exact (hregular (K.cutPair m).1 (K.cutPair m).2 hleft₀ hdisjoint hcover
      (fun θ => (hcut false θ).2) σ p hp).of_le (by simp)
  · intro p hp
    have hcov : physicalPieceOpen S K z (K.cutPair m).2 ∪
        physicalPieceOpen S K z (K.cutPair m).1 = N \ Γ := by
      simpa only [union_comm] using hcover
    exact ((hregular (K.cutPair m).2 (K.cutPair m).1 hleft₁ hdisjoint.symm hcov
      (fun θ => (hcut true θ).2) (-σ) p hp).add contDiffAt_const).of_le (by simp)
  · rintro p ⟨_, θ, rfl⟩
    have hF₀ := ((hA.boundary z hz hs (K.cutPair m).1).2.2.2.2.1 _
      (hcut false θ).1).1
    have hF₁ := ((hA.boundary z hz hs (K.cutPair m).2).2.2.2.2.1 _
      (hcut true θ).1).1
    exact airyFirstIntegrals_match_of_reflected_derivative
      (hF₀.differentiableAt (by simp)) (hF₁.differentiableAt (by simp))
      hρ (hcut false θ).2 (hcut true θ).2
      (canonicalCut_height_and_firstJets hA hB hz hs m θ).2.2.2 σ

end ContinuousFlexibility.Analysis
