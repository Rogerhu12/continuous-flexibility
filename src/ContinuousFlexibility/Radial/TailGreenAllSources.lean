import ContinuousFlexibility.Analysis.L2KernelRepresentation
import ContinuousFlexibility.Radial.TailFormIdentification
import ContinuousFlexibility.Radial.TailGreenL2Representation
import ContinuousFlexibility.Radial.TailNaturalUniqueness

/-!
# The actual fundamental Green kernel for every weighted L² source

The left state is used only on a compact initial segment in each row.
The right state is the actual square-integrable natural solution. This
proves row-wise L² membership and extends the proved test representation
of the Friedrichs inverse without any all-source representation input.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- The same normalized pair represents the actual Friedrichs inverse
for arbitrary L² input. Natural-line uniqueness and form identification
are proved upstream, rather than added as hypotheses here. -/
theorem tailFundamentalGreen_representation_L2 {T : DeepTailData}
    [IsLocallyFiniteMeasure (deepTailMeasure T)]
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (hG : ∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f))
    {u q w z : ℝ → ℝ} (hu : TailNaturalEquation T u)
    (hua : u T.entrance ≠ 0) (hunode : ∀ n, u (T.node n) ≠ 0)
    (hwc : ContinuousOn w (Ico T.entrance T.endpoint))
    (hus : TailFirstOrderSystem T.p T.Λ u q (Ico T.entrance T.endpoint))
    (hws : TailFirstOrderSystem T.p T.Λ w z (Ico T.entrance T.endpoint))
    (hwa : w T.entrance = 0)
    (hW : ∀ x ∈ Ico T.entrance T.endpoint, z x * u x - w x * q x = 1)
    (f : DeepTailL2 T) :
    (G f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => ∫ y,
      tailFundamentalGreenKernel T.entrance T.endpoint w u 1 x y * f y
        ∂deepTailMeasure T := by
  have hp := deepTail_contDiffOn hT
  have hpos := deepTail_pos hT
  have hI : TailFormIdentification T T.endpoint :=
    tailFormIdentification (hp.mono Ioo_subset_Ico_self)
      (fun x hx => hpos x (Ioo_subset_Ico_self hx)) le_rfl
  have hUnique : ∀ v, TailNaturalEquation T v → ∃ c : ℝ,
      ∀ x ∈ Ioo T.entrance T.endpoint, v x = c * u x := by
    intro v hv
    exact ⟨v (T.node 0) / u (T.node 0),
      tailNaturalEquation_eq_mul hT hη hK hu hv hunode⟩
  have hfull : ∀ᵐ x ∂deepTailMeasure T, x ∈ Ioo T.entrance T.endpoint :=
    (withDensity_absolutelyContinuous (volume.restrict (Ioo T.entrance T.endpoint))
      (fun x => ENNReal.ofReal (T.p x))).ae_le (ae_restrict_mem measurableSet_Ioo)
  have huc : ContinuousOn u (Ico T.entrance T.endpoint) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with heq | hlt
    · subst x
      exact hu.1.continuousAt.continuousWithinAt
    · exact (hu.2.1.contDiffAt (isOpen_Ioo.mem_nhds ⟨hlt, hx.2⟩)).continuousAt.continuousWithinAt
  have hrow : ∀ᵐ x ∂deepTailMeasure T,
      MemLp (fun y => tailFundamentalGreenKernel T.entrance T.endpoint w u 1 x y)
        2 (deepTailMeasure T) := hfull.mono fun x hx =>
    tailFundamentalGreenKernel_memLp_row hp hpos hwc huc hu.2.2.1 x
  exact l2Kernel_representation_of_smooth_tests isOpen_Ioo hfull G _ hrow
    (tailFundamentalGreen_compact_representation hT hI G hG hu hua hUnique
      hwc hus hws hwa hW) f

end ContinuousFlexibility.Radial
