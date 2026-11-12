import ContinuousFlexibility.Analysis.CanonicalGluedAiryIntegral
import ContinuousFlexibility.Analysis.CanonicalCutEndpointSeparation
import ContinuousFlexibility.Analysis.AiryHalfHolonomy

/-!
# True endpoint traces of the glued Airy first integral

A continuous physical path approaching an outer root is eventually in
that root's actual open half. This follows from the exclusion of the
opposite root from the other closed half. The limit is therefore the
genuine closed chart trace, regardless of the total chart values outside
its physical domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Every point of the actual outer root circle belongs to its own closed
half and has canonical radial coordinate zero. -/
theorem canonicalCutPair_root_mem_closed_and_zero
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    (c, θ) ∈ physicalPieceClosed S K z i ∧ (K.chart z i (c, θ)).1 = 0 := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  obtain ⟨_, _, _, _, _, hρ, hlL, hlR, hrL, hrR⟩ := hB.1.1 m
  have hleft : K.left i = 0 := by cases side <;> assumption
  have hright : K.right i = K.cutRadius m := by cases side <;> assumption
  have hzero : K.inverseChart z i '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
      ({c} ×ˢ (univ : Set ℝ)) := by
    cases side
    · exact (hB.1.2 z hz hs m).2.2.2.2.1
    · exact (hB.1.2 z hz hs m).2.2.2.2.2
  have hpImage : (c, θ) ∈ K.inverseChart z i '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) := by
    rw [hzero]
    exact ⟨rfl, mem_univ _⟩
  obtain ⟨q, hq, hqp⟩ := hpImage
  have hq0 : q.1 = 0 := hq.1
  have hqC : q ∈ canonicalClosed S K i := by
    refine ⟨?_, mem_univ _⟩
    simpa only [Set.mem_Icc, hleft, hright, hq0] using And.intro (le_refl (0 : ℝ)) hρ.le
  have hboundary := hA.boundary z hz hs i
  have hF : K.chart z i (c, θ) = q := by
    simpa only [hqp] using hboundary.2.2.2.1 q hqC
  exact ⟨hqp ▸ hboundary.2.1 hqC, by rw [hF]; exact hq0⟩

/-- A continuous trajectory is eventually in the correct actual half as
it approaches either outer endpoint through the open component. -/
theorem canonicalCutPair_path_eventually_mem_own_half
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc (C.left m) (C.right m))) :
    ∀ᶠ r in 𝓝[Ioo (C.left m) (C.right m)]
      (if side then C.right m else C.left m),
      (r, u r) ∈ physicalPieceOpen S K z
        (if side then (K.cutPair m).2 else (K.cutPair m).1) := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let j := if side then (K.cutPair m).1 else (K.cutPair m).2
  let c := if side then C.right m else C.left m
  let N : Set PolarPoint := Ioo (C.left m) (C.right m) ×ˢ univ
  let Γ : Set PolarPoint := Set.range (canonicalCutPoint S K z m)
  have hcurrent := hB.1.2 z hz hs m
  have hcomponent := hcurrent.2.1 (mem_range_self (0 : ℝ))
  have hab : C.left m < C.right m := hcomponent.1.1.trans hcomponent.1.2
  have hc : c ∈ Icc (C.left m) (C.right m) := by
    cases side
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  have hnot : (c, u c) ∉ physicalPieceClosed S K z j := by
    cases side
    · exact canonicalCutPair_opposite_endpoint_not_mem_closed hA hB.1 hz hs m true _
    · exact canonicalCutPair_opposite_endpoint_not_mem_closed hA hB.1 hz hs m false _
  have hpath : ContinuousOn (fun r : ℝ => (r, u r)) (Icc (C.left m) (C.right m)) :=
    continuousOn_id.prodMk hu
  have ht : Tendsto (fun r : ℝ => (r, u r))
      (𝓝[Ioo (C.left m) (C.right m)] c) (𝓝 (c, u c)) :=
    (hpath c hc).mono Ioo_subset_Icc_self
  have havoid : ∀ᶠ r in 𝓝[Ioo (C.left m) (C.right m)] c,
      (r, u r) ∉ physicalPieceClosed S K z j :=
    ht.eventually (isClosed_closure.isOpen_compl.mem_nhds hnot)
  have hcover : physicalPieceOpen S K z i ∪ physicalPieceOpen S K z j = N \ Γ := by
    cases side
    · exact hcurrent.2.2.2.1
    · change physicalPieceOpen S K z (K.cutPair m).2 ∪
        physicalPieceOpen S K z (K.cutPair m).1 =
        (Ioo (C.left m) (C.right m) ×ˢ univ) \ Set.range (canonicalCutPoint S K z m)
      rw [union_comm]
      exact hcurrent.2.2.2.1
  have hΓ : Γ ⊆ physicalPieceClosed S K z j := by
    rintro p ⟨θ, rfl⟩
    cases side
    · exact (canonicalCut_closed_and_chart hA hB hz hs m true θ).1
    · exact (canonicalCut_closed_and_chart hA hB hz hs m false θ).1
  filter_upwards [havoid, self_mem_nhdsWithin] with r hr hrab
  have hcut : (r, u r) ∉ Γ := fun h => hr (hΓ h)
  have hp : (r, u r) ∈ physicalPieceOpen S K z i ∪ physicalPieceOpen S K z j := by
    rw [hcover]
    exact ⟨⟨hrab, mem_univ _⟩, hcut⟩
  exact hp.elim id (fun h => (hr (subset_closure h)).elim)

/-- The true one-sided endpoint trace of the glued integral. No value of
the glued function at that endpoint is asserted. -/
theorem canonicalGluedAiryIntegral_tendsto_endpoint
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (σ : ℝ) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc (C.left m) (C.right m))) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    Tendsto (fun r => canonicalGluedAiryIntegral S K z m σ (r, u r))
      (𝓝[Ioo (C.left m) (C.right m)] c)
      (𝓝 ((K.chart z i (c, u c)).2 +
        if side then 2 * σ * airyTravelPrimitive (K.cutRadius m) else 0)) := by
  classical
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  let τ : ℝ := if side then -σ else σ
  let offset : ℝ := if side then 2 * σ * airyTravelPrimitive (K.cutRadius m) else 0
  have hroot := canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m side (u c)
  have hF : ContinuousAt (K.chart z i) (c, u c) :=
    ((hA.boundary z hz hs i).2.2.2.2.1 _ hroot.1).1.continuousAt
  have hcomponent := (hB.1.2 z hz hs m).2.1 (mem_range_self (0 : ℝ))
  have hab : C.left m < C.right m := hcomponent.1.1.trans hcomponent.1.2
  have hc : c ∈ Icc (C.left m) (C.right m) := by
    cases side
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  have hpath : ContinuousOn (fun r : ℝ => (r, u r)) (Icc (C.left m) (C.right m)) :=
    continuousOn_id.prodMk hu
  have ht : Tendsto (fun r : ℝ => (r, u r))
      (𝓝[Ioo (C.left m) (C.right m)] c) (𝓝 (c, u c)) :=
    (hpath c hc).mono Ioo_subset_Icc_self
  have hFt := hF.tendsto.comp ht
  have hFr : Tendsto (fun r => (K.chart z i (r, u r)).1)
      (𝓝[Ioo (C.left m) (C.right m)] c) (𝓝 ((K.chart z i (c, u c)).1)) :=
    (continuous_fst.tendsto (K.chart z i (c, u c))).comp hFt
  have hFa : Tendsto (fun r => (K.chart z i (r, u r)).2)
      (𝓝[Ioo (C.left m) (C.right m)] c) (𝓝 ((K.chart z i (c, u c)).2)) :=
    (continuous_snd.tendsto (K.chart z i (c, u c))).comp hFt
  have hlim : Tendsto
      (fun r => airyFirstIntegral (K.chart z i) τ (r, u r) + offset)
      (𝓝[Ioo (C.left m) (C.right m)] c)
      (𝓝 ((K.chart z i (c, u c)).2 +
        τ * airyTravelPrimitive (K.chart z i (c, u c)).1 + offset)) :=
    (hFa.add (tendsto_const_nhds.mul
      ((continuous_airyTravelPrimitive.tendsto _).comp hFr))).add tendsto_const_nhds
  have he : (fun r => airyFirstIntegral (K.chart z i) τ (r, u r) + offset) =ᶠ[
      𝓝[Ioo (C.left m) (C.right m)] c]
      (fun r => canonicalGluedAiryIntegral S K z m σ (r, u r)) := by
    filter_upwards [canonicalCutPair_path_eventually_mem_own_half hA hB hz hs m side hu]
      with r hr
    cases side
    · change airyFirstIntegral (K.chart z (K.cutPair m).1) σ (r, u r) + 0 =
        canonicalGluedAiryIntegral S K z m σ (r, u r)
      rw [add_zero]
      exact (piecewise_eq_of_mem _ _ _ hr).symm
    · have hnot : (r, u r) ∉ physicalPieceOpen S K z (K.cutPair m).1 :=
        fun h => Set.disjoint_left.mp (hB.1.2 z hz hs m).2.2.1 h hr
      change airyFirstIntegral (K.chart z (K.cutPair m).2) (-σ) (r, u r) +
          2 * σ * airyTravelPrimitive (K.cutRadius m) =
        canonicalGluedAiryIntegral S K z m σ (r, u r)
      exact (piecewise_eq_of_notMem _ _ _ hnot).symm
  have hzero : (K.chart z i (c, u c)).1 = 0 := hroot.2
  change Tendsto (fun r => canonicalGluedAiryIntegral S K z m σ (r, u r))
    (𝓝[Ioo (C.left m) (C.right m)] c)
    (𝓝 ((K.chart z i (c, u c)).2 + offset))
  rw [hzero, airyTravelPrimitive_zero, mul_zero, add_zero] at hlim
  exact hlim.congr' he

end ContinuousFlexibility.Analysis
