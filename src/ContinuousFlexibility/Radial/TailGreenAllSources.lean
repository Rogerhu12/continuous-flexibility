import ContinuousFlexibility.Analysis.L2KernelRepresentation
import ContinuousFlexibility.Radial.TailFormIdentification
import ContinuousFlexibility.Radial.TailFundamentalGreenRepresentation
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

theorem tailFundamentalGreenKernel_memLp_row_allSources {T : DeepTailData}
    {w u : ℝ → ℝ} {W x : ℝ}
    (hp : ContinuousOn T.p (Ico T.entrance T.endpoint))
    (hp₀ : ∀ y ∈ Ico T.entrance T.endpoint, 0 ≤ T.p y)
    (hw : ContinuousOn w (Ico T.entrance T.endpoint))
    (hu : MemLp u 2 (deepTailMeasure T)) (hx : x ∈ Ioo T.entrance T.endpoint) :
    MemLp (fun y => tailFundamentalGreenKernel T.entrance T.endpoint w u W x y)
      2 (deepTailMeasure T) := by
  have hwm : AEStronglyMeasurable w
      ((deepTailMeasure T).restrict (Ioo T.entrance x)) :=
    (hw.mono (fun y hy => ⟨hy.1.le, hy.2.trans hx.2⟩)).aestronglyMeasurable
      measurableSet_Ioo
  have hwsq : IntegrableOn (fun y => w y ^ 2) (Ioo T.entrance x) (deepTailMeasure T) :=
    tail_left_solution_integrableOn hp hp₀ (hw.pow 2) hx
  have hwLp : MemLp w 2 ((deepTailMeasure T).restrict (Ioo T.entrance x)) :=
    (memLp_two_iff_integrable_sq hwm).mpr hwsq
  have hleft : MemLp ((Ioo T.entrance x).indicator (fun t => (u x / W) * w t))
      2 (deepTailMeasure T) := (memLp_indicator_iff_restrict measurableSet_Ioo).mpr
    (hwLp.const_mul (u x / W))
  have hright : MemLp ((Ico x T.endpoint).indicator (fun t => (w x / W) * u t))
      2 (deepTailMeasure T) := MemLp.indicator measurableSet_Ico (hu.const_mul (w x / W))
  have heq : (fun y =>
      (Ioo T.entrance x).indicator (fun t => (u x / W) * w t) y +
        (Ico x T.endpoint).indicator (fun t => (w x / W) * u t) y) =ᵐ[deepTailMeasure T]
      fun y => tailFundamentalGreenKernel T.entrance T.endpoint w u W x y :=
    Eventually.of_forall fun y => (tailFundamentalGreenKernel_row_split hx y).symm
  exact (memLp_congr_ae heq).mp (hleft.add hright)

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
  have hrow : ∀ᵐ x ∂deepTailMeasure T,
      MemLp (fun y => tailFundamentalGreenKernel T.entrance T.endpoint w u 1 x y)
        2 (deepTailMeasure T) := hfull.mono fun x hx =>
    tailFundamentalGreenKernel_memLp_row_allSources hp.continuousOn
      (fun y hy => (hpos y hy).le) hwc hu.2.2.1 hx
  exact l2Kernel_representation_of_smooth_tests isOpen_Ioo hfull G _ hrow
    (tailFundamentalGreen_compact_representation hT hI G hG hu hua hUnique
      hwc hus hws hwa hW) f

end ContinuousFlexibility.Radial
