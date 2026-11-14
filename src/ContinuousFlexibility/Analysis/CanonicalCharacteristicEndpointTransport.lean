module

public import ContinuousFlexibility.Analysis.CanonicalGluedAiryTransport
public import ContinuousFlexibility.Analysis.CanonicalGluedAiryEndpointTrace
public import ContinuousFlexibility.Analysis.CanonicalCutAxis
public import ContinuousFlexibility.Analysis.TwoExceptionalRadiiTrace

/-!
# Full-component transport along an actual characteristic

The glued first integral is C¹ throughout the open negative component.
Its actual derivative along the chosen characteristic vanishes except
possibly at the two fixed radii where the cut meets the fundamental axes.
The two exceptional-radius theorem then equates the genuine endpoint
traces. No bound on the number of cut crossings is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem canonicalGluedAiryIntegral_endpoint_of_actual_ode
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {u : ℝ → ℝ} (hu : ContinuousOn u (Icc (C.left m) (C.right m)))
    (hflow : ∀ r ∈ Ioo (C.left m) (C.right m),
      HasDerivAt u ((L.coefficients z).b (r, u r) / (L.coefficients z).a (r, u r) -
        σ * Real.sqrt ((L.coefficients z).b (r, u r) ^ 2 -
          (L.coefficients z).a (r, u r) * (L.coefficients z).c (r, u r)) /
            (L.coefficients z).a (r, u r)) r) :
    (K.chart z (K.cutPair m).2 (C.right m, u (C.right m))).2 +
        2 * σ * airyTravelPrimitive (K.cutRadius m) =
      (K.chart z (K.cutPair m).1 (C.left m, u (C.left m))).2 := by
  let U : PolarPoint → ℝ := canonicalGluedAiryIntegral S K z m σ
  let N : Set PolarPoint := Ioo (C.left m) (C.right m) ×ˢ univ
  let c : ℝ := (canonicalCutPoint S K z m 0).1
  let d : ℝ := (canonicalCutPoint S K z m (Real.pi / 2)).1
  have hN : IsOpen N := isOpen_Ioo.prod isOpen_univ
  have hU : ContDiffOn ℝ 1 U N := contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m σ
  have hc : c ∈ Ioo (C.left m) (C.right m) :=
    ((hB.1.2 z hz hs m).2.1 (mem_range_self (0 : ℝ))).1
  have hd : d ∈ Ioo (C.left m) (C.right m) :=
    ((hB.1.2 z hz hs m).2.1 (mem_range_self (Real.pi / 2))).1
  have hpath : ContinuousOn (fun r : ℝ => (r, u r)) (Ioo (C.left m) (C.right m)) :=
    continuousOn_id.prodMk (hu.mono Ioo_subset_Icc_self)
  have hf : ContinuousOn (fun r => U (r, u r)) (Ioo (C.left m) (C.right m)) :=
    hU.continuousOn.comp hpath (fun r hr => ⟨hr, mem_univ _⟩)
  have hzero (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m))
      (hrc : r ≠ c) (hrd : r ≠ d) : HasDerivAt (fun t => U (t, u t)) 0 r := by
    have hp : (r, u r) ∈ N := ⟨hr, mem_univ _⟩
    have haxis : (r, u r) ∈ Set.range (canonicalCutPoint S K z m) →
        Real.sin (2 * (r, u r).2) ≠ 0 := by
      intro hcut hsin
      rcases canonicalCut_axis_radial_cases hA hB.1.1 hz hs m hcut hsin with h | h
      · exact hrc h
      · exact hrd h
    have htransport := canonicalGluedAiryIntegral_characteristic_transport
      hS hT hN01 hN03 hA hB hz hs m hσ hp haxis
    have hUd : DifferentiableAt ℝ U (r, u r) :=
      ((hU (r, u r) hp).contDiffAt (hN.mem_nhds hp)).differentiableAt_one
    have hcurve := (hasDerivAt_id r).prodMk (hflow r hr)
    have hh := hUd.hasFDerivAt.comp_hasDerivAt r hcurve
    have he : U ∘ (fun t : ℝ => (t, u t)) = (fun t : ℝ => U (t, u t)) := by
      funext t
      exact Function.comp_apply
    simp only [id_eq] at hh
    rw [he] at hh
    apply hh.congr_deriv
    rw [polarCLM_apply_decompose]
    change 1 * radialPartial U (r, u r) +
      ((L.coefficients z).b (r, u r) / (L.coefficients z).a (r, u r) -
        σ * Real.sqrt ((L.coefficients z).b (r, u r) ^ 2 -
          (L.coefficients z).a (r, u r) * (L.coefficients z).c (r, u r)) /
            (L.coefficients z).a (r, u r)) * angularPartial U (r, u r) = 0
    rw [htransport]
    ring
  have hleft : Tendsto (fun r => U (r, u r))
      (𝓝[Ioo (C.left m) (C.right m)] (C.left m))
      (𝓝 ((K.chart z (K.cutPair m).1 (C.left m, u (C.left m))).2)) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
      canonicalGluedAiryIntegral_tendsto_endpoint hA hB hz hs m false σ hu
  have hright : Tendsto (fun r => U (r, u r))
      (𝓝[Ioo (C.left m) (C.right m)] (C.right m))
      (𝓝 ((K.chart z (K.cutPair m).2 (C.right m, u (C.right m))).2 +
        2 * σ * airyTravelPrimitive (K.cutRadius m))) :=
    canonicalGluedAiryIntegral_tendsto_endpoint hA hB hz hs m true σ hu
  exact endpoint_traces_eq_of_hasDerivAt_zero_off_pair hc hd hf hzero hleft hright

end ContinuousFlexibility.Analysis
