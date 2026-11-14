import ContinuousFlexibility.Analysis.CanonicalGluedAiryIntegral
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Extending actual angular bounds to an interior section's endpoints

The glued first integral is genuinely C¹ on the whole negative
component. Its angular derivative is therefore continuous at both
endpoints of any strictly interior radial interval. Bounds proved on
the open interval extend to its closure with the same constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

theorem canonicalGluedAiryIntegral_angular_bounds_closedStrip
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (σ : ℝ)
    {a b l u : ℝ} (ha : C.left m < a) (hab : a < b) (hb : b < C.right m)
    (hbound : ∀ r ∈ Ioo a b, ∀ θ : ℝ,
      angularPartial (canonicalGluedAiryIntegral S K z m σ) (r, θ) ∈ Icc l u)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    angularPartial (canonicalGluedAiryIntegral S K z m σ) (r, θ) ∈ Icc l u := by
  have hq : (r, θ) ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    ⟨⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩, mem_univ _⟩
  have hdiff := ((contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m σ)
    (r, θ) hq).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)
  have hc : ContinuousAt (angularPartial (canonicalGluedAiryIntegral S K z m σ)) (r, θ) :=
    (hdiff.continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hclosure : r ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact hr
  have : NeBot (𝓝[Ioo a b] r) := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hline : ContinuousAt (fun s : ℝ => (s, θ)) r :=
    continuousAt_id.prodMk continuousAt_const
  have ht : Tendsto
      (fun s : ℝ => angularPartial (canonicalGluedAiryIntegral S K z m σ) (s, θ))
      (𝓝[Ioo a b] r)
      (𝓝 (angularPartial (canonicalGluedAiryIntegral S K z m σ) (r, θ))) :=
    (ContinuousAt.comp (f := fun s : ℝ => (s, θ)) (x := r) hc hline).mono_left
      nhdsWithin_le_nhds
  have he : ∀ᶠ s in 𝓝[Ioo a b] r,
      angularPartial (canonicalGluedAiryIntegral S K z m σ) (s, θ) ∈ Icc l u := by
    filter_upwards [self_mem_nhdsWithin] with s hss
    exact hbound s hss θ
  exact ⟨ge_of_tendsto ht (he.mono fun _ h => h.1),
    le_of_tendsto ht (he.mono fun _ h => h.2)⟩

end ContinuousFlexibility.Analysis
