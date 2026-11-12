import ContinuousFlexibility.Analysis.ScalarEquationBoundaryContinuity
import ContinuousFlexibility.Analysis.CanonicalStoredSliceBijection
import ContinuousFlexibility.Analysis.CanonicalBoundaryLift

/-!
# Joint root continuity of the original stored N03 flow

The actual first-integral equation determines every stored angular
slice. Its fixed-angle endpoint traces, together with continuous
injective interior slices and the strictly increasing boundary lift,
give the joint initial-angle/radial limit. The Airy primitive is used
only continuously at zero; no smoothness there is asserted.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The true stored family has its joint endpoint limit. In particular,
the radius in a root coefficient germ can be made uniform over a small
neighborhood of a fixed initial angle, without a field certificate. -/
theorem n03_minusFlow_tendsto_root_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (ι : ℝ) :
    Tendsto (fun p : PolarPoint => L.minusFlow z m p.1 p.2)
      (𝓝[Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)]
        (if side then C.right m else C.left m, ι))
      (𝓝 (L.minusFlow z m (if side then C.right m else C.left m) ι)) := by
  let c := if side then C.right m else C.left m
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let N := Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
  let l : Filter PolarPoint := 𝓝[N] (c, ι)
  let U := canonicalGluedAiryIntegral S K z m (1 : ℝ)
  let α : ℝ → ℝ := fun θ => (K.chart z (K.cutPair m).1 (C.left m, θ)).2
  let G : ℝ → ℝ := fun θ => (K.chart z i (c, θ)).2 +
    if side then 2 * airyTravelPrimitive (K.cutRadius m) else 0
  have hroot (θ : ℝ) := canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m side θ
  have hleft (θ : ℝ) := canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m false θ
  have hb := canonicalBoundaryAngular_bijective hA hz hs i
    (fun θ => (hroot θ).1) (fun θ => (hroot θ).2)
  have hl := canonicalBoundaryAngular_bijective hA hz hs (K.cutPair m).1
    (fun θ => (hleft θ).1) (fun θ => (hleft θ).2)
  have hG : StrictMono G := by
    intro θ η hθη
    exact add_lt_add_right ((strictMono_of_deriv_pos hb.2.1) hθη) _
  have hfst : Tendsto (fun p : PolarPoint => p.1) l
      (𝓝[Ioo (C.left m) (C.right m)] c) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_fst.continuousWithinAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.1
  have hfixed (θ : ℝ) : Tendsto (fun p : PolarPoint => U (p.1, θ)) l (𝓝 (G θ)) := by
    have ht := canonicalGluedAiryIntegral_tendsto_endpoint hA hB hz hs m side (1 : ℝ)
      (u := fun _ : ℝ => θ) continuousOn_const
    have ht' : Tendsto (fun r => U (r, θ))
        (𝓝[Ioo (C.left m) (C.right m)] c) (𝓝 (G θ)) := by
      simpa only [mul_one] using ht
    exact ht'.comp hfst
  have hU := contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m (1 : ℝ)
  have hcont : ∀ᶠ p : PolarPoint in l, Continuous (fun θ => U (p.1, θ)) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hUat : ContinuousAt U (p.1, θ) := hU.continuousOn.continuousAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp.1, mem_univ θ⟩)
    have hline : ContinuousAt (fun η : ℝ => (p.1, η)) θ :=
      (continuous_const.prodMk continuous_id).continuousAt
    exact ContinuousAt.comp (f := fun η : ℝ => (p.1, η)) (x := θ) hUat hline
  have hinj : ∀ᶠ p : PolarPoint in l, Function.Injective (fun θ => U (p.1, θ)) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact canonicalGluedAiryIntegral_angular_injective hS hT hN01 hN03 hA hB hz hs m
      (σ := 1) (Or.inl rfl) hp.1
  have heq : ∀ᶠ p : PolarPoint in l, U (p.1, L.minusFlow z m p.1 p.2) = α p.2 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hflow := hN03.2.2.2.2.1 z hz hs m p.2
    have hh := canonicalGluedAiryIntegral_of_actual_ode hS hT hN01 hN03 hA hB hz hs m
      (σ := 1) (Or.inl rfl) hflow.2.1 (fun r hr => by
        simpa only [minusCharacteristicSpeed, one_mul] using hflow.2.2.1 r hr) hp.1
    rw [hflow.1] at hh
    exact hh
  have hboundary : G (L.minusFlow z m c ι) = α ι := by
    cases side
    · change (K.chart z (K.cutPair m).1
        (C.left m, L.minusFlow z m (C.left m) ι)).2 + 0 = _
      rw [(hN03.2.2.2.2.1 z hz hs m ι).1, add_zero]
    · have hh := (canonicalRootAngles_of_n03Flows hS hT hN01 hN03 hA hB hz hs m ι).1
      have hh' : (K.chart z (K.cutPair m).2
          (C.right m, L.minusFlow z m (C.right m) ι)).2 =
        α ι - 2 * airyTravelPrimitive (K.cutRadius m) := hh
      change (K.chart z (K.cutPair m).2
        (C.right m, L.minusFlow z m (C.right m) ι)).2 +
          2 * airyTravelPrimitive (K.cutRadius m) = α ι
      linarith only [hh']
  have htarget : Tendsto (fun p : PolarPoint => α p.2) l
      (𝓝 (G (L.minusFlow z m c ι))) := by
    rw [hboundary]
    exact (hl.1.continuous.tendsto ι).comp continuous_snd.continuousWithinAt
  exact tendsto_of_injective_scalar_equation hcont hinj heq hfixed htarget hG

end ContinuousFlexibility.Analysis
