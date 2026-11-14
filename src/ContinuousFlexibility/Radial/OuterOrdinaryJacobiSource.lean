module

public import ContinuousFlexibility.Radial.OuterActualInverseAssertions
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The same outer inverse for ordinary compactly supported Jacobi sources

For an interior compact source `f`, the weighted source is `-f / ρ`.
Its actual weighted L² membership follows from continuity and compact
support.  Applying the same Robin inverse gives the ordinary kernel
`-∫ K f`, the original Jacobi equation, and the same boundary conditions.
No global unweighted L² bound is asserted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem outerOrdinarySource_memLp
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {entry : ℝ} (hentry : entry ∈ radialCore D)
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    MemLp (fun x => -f x / outerWholeDensity D right x) 2
      (outerWholeMeasure D right entry) := by
  let g : ℝ → ℝ := fun x => -f x / outerWholeDensity D right x
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ tsupport f
    · have hxi := Ioo_subset_Ico_self (hs hx)
      have hR : Continuous (outerOutwardRadius right) := by
        cases right
        · exact continuous_id.neg
        · exact continuous_id
      have hρ : ContinuousAt (outerWholeDensity D right) x :=
        (continuous_const.mul
          ((matchingProfileGeometry hD).2.2.1.1.continuous.comp hR)).continuousAt.div
            (continuousAt_id.pow 2)
            (pow_ne_zero 2 (outerWhole_coordinate_ne_zero (matchingProfileGeometry hD)
              hentry hxi))
      exact hf.continuousAt.neg.div hρ (outerWholeDensity_pos hD hentry hxi).ne'
    · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
      simp only [g, image_eq_zero_of_notMem_tsupport hy, neg_zero, zero_div]
  have hgc : HasCompactSupport g := by
    apply hc.mono
    intro x hx
    show f x ≠ 0
    intro hfx
    exact hx (by simp only [g, hfx, neg_zero, zero_div])
  letI := outerWholeMeasure_isFinite hD right entry
  exact hg.memLp_of_hasCompactSupport hgc

def outerOrdinaryWeightedSource
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {entry : ℝ} (hentry : entry ∈ radialCore D)
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    OuterWholeL2 D right entry :=
  (outerOrdinarySource_memLp hD hentry hf hc hs).toLp
    (fun x => -f x / outerWholeDensity D right x)

theorem outerOrdinaryWeightedSource_ae
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {entry : ℝ} (hentry : entry ∈ radialCore D)
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    (outerOrdinaryWeightedSource hD hentry hf hc hs : ℝ → ℝ)
      =ᵐ[outerWholeMeasure D right entry] fun x => -f x / outerWholeDensity D right x :=
  (outerOrdinarySource_memLp hD hentry hf hc hs).coeFn_toLp

/-- The density and sign cancel in every ordinary source pairing. -/
theorem outerOrdinaryWeightedSource_integral
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {entry : ℝ} (hentry : entry ∈ radialCore D)
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) (W : ℝ → ℝ) :
    (∫ y, W y * outerOrdinaryWeightedSource hD hentry hf hc hs y
      ∂outerWholeMeasure D right entry) =
      -(∫ y in (outerOutwardRadius right entry)..
        (outerOutwardRadius right (tailPhysicalEndpoint D right)), W y * f y) := by
  rw [outerWholeDensity_integral hD hentry, ← intervalIntegral.integral_neg]
  simp only [intervalIntegral.integral_of_le (outerWhole_interval hentry).le,
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [(outerWholeMeasure_ae_iff hD hentry).mp
    (outerOrdinaryWeightedSource_ae hD hentry hf hc hs), ae_restrict_mem measurableSet_Ioo]
    with y hy hyi
  rw [hy]
  field_simp [(outerWholeDensity_pos hD hentry (Ioo_subset_Ico_self hyi)).ne'] <;> ring

namespace OuterPhysicalRobinInverse

variable {M : MorseChainData} {D : ReferenceData}
  {right : Bool} {j start : ℕ} {entry deep η K lam : ℝ}
  {F : MorsePhysicalTailBasis M D right j start deep η K}
  {H : OuterFundamentalStatePair
    (fun x => lam / outerTailOutwardWeight D right x)
    (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
    F.P (F.ZP lam) F.Q (F.ZQ lam)
    (outerOutwardRadius right entry) (outerOutwardRadius right deep)
    (outerOutwardRadius right (tailPhysicalEndpoint D right))}

/-- Applying the same weighted inverse to `-f / ρ` inverts the ordinary
Jacobi expression on compact interior sources.  Both the ordinary kernel
and the boundary assertions refer to that exact solution. -/
theorem ordinary_jacobi_source (I : OuterPhysicalRobinInverse F H)
    (hD : IsAccumulatingProfile D) (hentry : entry ∈ radialCore D)
    (hlam : lam ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    let a := outerOutwardRadius right entry
    let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
    let w := outerTailOutwardWeight D right
    let source := outerOrdinaryWeightedSource hD hentry hf.continuous hc hs
    let g := outerPhysicalGreenValue D right entry lam H.U H.V source
    (I.operator source : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] g ∧
    MemLp g 2 (outerWholeMeasure D right entry) ∧ ContDiffOn ℝ 1 g (Ico a b) ∧
    ((I.operator source : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      fun x => -(∫ y in a..b, outerGreenKernel lam H.U H.V x y * f y)) ∧
    outerStatePair H.entrance (g a, w a * derivWithin g (Ico a b) a / lam) = 0 ∧
    outerStatePair (outerStatePerp H.entrance)
      (g a, w a * derivWithin g (Ico a b) a / lam) =
        -(∫ y in a..b, H.V y * f y) / lam ∧
    Tendsto (fun x => g x * (w x * deriv H.V x) - w x * deriv g x * H.V x)
      (𝓝[<] b) (𝓝 0) ∧
    ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, (I.operator source) x * radialJacobi ((j : ℝ) ^ 2) w ψ x) =
        ∫ x in a..b, f x * ψ x := by
  let a := outerOutwardRadius right entry
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let source := outerOrdinaryWeightedSource hD hentry hf.continuous hc hs
  obtain ⟨hae, hmem, hreg, hRobin, htrace, hbracket, hpair⟩ :=
    (I.assertions hD hentry hlam).2 source
  have hkernel : (I.operator source : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      fun x => -(∫ y in a..b, outerGreenKernel lam H.U H.V x y * f y) := by
    apply (outerWholeMeasure_ae_iff hD hentry).mp
    filter_upwards [I.kernel source] with x hx
    exact hx.trans (outerOrdinaryWeightedSource_integral hD hentry hf.continuous hc hs
      (outerGreenKernel lam H.U H.V x))
  refine ⟨hae, hmem, hreg, hkernel, hRobin, ?_, hbracket, ?_⟩
  · exact htrace.trans (congrArg (fun t : ℝ => t / lam)
      (outerOrdinaryWeightedSource_integral hD hentry hf.continuous hc hs H.V))
  · intro ψ hψ hψc hψs
    refine (hpair ψ hψ hψc hψs).trans ?_
    rw [← intervalIntegral.integral_neg]
    simp only [intervalIntegral.integral_of_le (outerWhole_interval hentry).le,
      integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [(outerWholeMeasure_ae_iff hD hentry).mp
      (outerOrdinaryWeightedSource_ae hD hentry hf.continuous hc hs),
      ae_restrict_mem measurableSet_Ioo] with x hx hxi
    change -(outerWholeDensity D right x * source x * ψ x) = f x * ψ x
    rw [hx]
    field_simp [(outerWholeDensity_pos hD hentry (Ioo_subset_Ico_self hxi)).ne'] <;> ring

end OuterPhysicalRobinInverse

end ContinuousFlexibility.Radial
