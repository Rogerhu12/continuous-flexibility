module

public import ContinuousFlexibility.Analysis.CanonicalGluedAiryIntegral

/-!
# The actual first derivative of the glued Airy integral

On either open half the derivative is the corresponding Airy derivative.
At the common cut the transmission law gives the same full first jet,
so the ordinary derivative of the piecewise function is the left jet.
This pointwise interface is independent of stored cut coefficient values.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem canonicalGluedAiryIntegral_fderiv_on_piece
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (σ : ℝ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K z (if side then (K.cutPair m).2 else (K.cutPair m).1)) :
    fderiv ℝ (canonicalGluedAiryIntegral S K z m σ) p =
      fderiv ℝ (airyFirstIntegral
        (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1))
        (if side then -σ else σ)) p := by
  classical
  cases side with
  | false =>
      have he : canonicalGluedAiryIntegral S K z m σ =ᶠ[𝓝 p]
          airyFirstIntegral (K.chart z (K.cutPair m).1) σ := by
        filter_upwards [(hA.domains z hz hs (K.cutPair m).1).1.mem_nhds hp] with q hq
        exact piecewise_eq_of_mem _ _ _ hq
      exact he.fderiv_eq
  | true =>
      change fderiv ℝ (canonicalGluedAiryIntegral S K z m σ) p =
        fderiv ℝ (airyFirstIntegral (K.chart z (K.cutPair m).2) (-σ)) p
      have he : canonicalGluedAiryIntegral S K z m σ =ᶠ[𝓝 p]
          (fun q => airyFirstIntegral (K.chart z (K.cutPair m).2) (-σ) q +
            2 * σ * airyTravelPrimitive (K.cutRadius m)) := by
        filter_upwards [(hA.domains z hz hs (K.cutPair m).2).1.mem_nhds hp] with q hq
        apply piecewise_eq_of_notMem
        exact fun hleft => Set.disjoint_left.mp (hB.1.2 z hz hs m).2.2.1 hleft hq
      rw [he.fderiv_eq, fderiv_add_const]

/-- The true cut first derivative is the common ordinary first jet of
the two actual half integrals, even if the cut is crossed infinitely often. -/
theorem canonicalGluedAiryIntegral_fderiv_on_cut
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (σ θ : ℝ) :
    fderiv ℝ (canonicalGluedAiryIntegral S K z m σ) (canonicalCutPoint S K z m θ) =
      fderiv ℝ (airyFirstIntegral (K.chart z (K.cutPair m).1) σ)
        (canonicalCutPoint S K z m θ) := by
  classical
  let p := canonicalCutPoint S K z m θ
  have hleft : p ∈ physicalPieceClosed S K z (K.cutPair m).1 ∧
      K.chart z (K.cutPair m).1 p = (K.cutRadius m, θ) :=
    canonicalCut_closed_and_chart hA hB hz hs m false θ
  have hright : p ∈ physicalPieceClosed S K z (K.cutPair m).2 ∧
      K.chart z (K.cutPair m).2 p = (K.cutRadius m, θ) :=
    canonicalCut_closed_and_chart hA hB hz hs m true θ
  have hρ := (hB.1.1 m).2.2.2.2.2.1
  have hFL := ((hA.boundary z hz hs (K.cutPair m).1).2.2.2.2.1 p hleft.1).1
  have hFR := ((hA.boundary z hz hs (K.cutPair m).2).2.2.2.2.1 p hright.1).1
  have hξL : 0 < (K.chart z (K.cutPair m).1 p).1 := by
    rw [hleft.2]
    exact hρ
  have hξR : 0 < (K.chart z (K.cutPair m).2 p).1 := by
    rw [hright.2]
    exact hρ
  have hf := (contDiffAt_airyFirstIntegral hFL hξL σ).differentiableAt (by simp)
  have hg := ((contDiffAt_airyFirstIntegral hFR hξR (-σ)).add
    (contDiffAt_const (c := 2 * σ * airyTravelPrimitive (K.cutRadius m)))).differentiableAt
      (by simp)
  have hmatch := airyFirstIntegrals_match_of_reflected_derivative
    (hFL.differentiableAt (by simp)) (hFR.differentiableAt (by simp)) hρ hleft.2 hright.2
    (canonicalCut_height_and_firstJets hA hB hz hs m θ).2.2.2 σ
  have hd := hasFDerivAt_piecewise_of_matching_jets
    (s := physicalPieceOpen S K z (K.cutPair m).1)
    hf.hasFDerivAt (hg.hasFDerivAt.congr_fderiv hmatch.2.symm) hmatch.1
  exact hd.fderiv

end ContinuousFlexibility.Analysis
