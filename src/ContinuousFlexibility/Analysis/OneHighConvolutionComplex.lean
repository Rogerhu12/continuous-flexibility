import ContinuousFlexibility.Analysis.OneHighConvolutionFinite
import Mathlib.Analysis.Convolution

/-!
# Complex convolution and the positive Young estimate

The complex convolution is the actual Bochner convolution. Its pointwise
extended norm is bounded by the positive convolution already estimated
above. This gives genuine `L¹` and `L²` membership with the exact constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Convolution

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G]
  [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G}
  [SFinite μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

/-- The ordinary complex-valued Bochner convolution. -/
def complexConvolution (μ : Measure G) (f g : G → ℂ) : G → ℂ :=
  f ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] g

theorem complexConvolution_apply (f g : G → ℂ) (x : G) :
    complexConvolution μ f g x = ∫ y, f y * g (x - y) ∂μ := rfl

theorem measurable_complexConvolution {f g : G → ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (complexConvolution μ f g) := by
  have h : StronglyMeasurable (fun p : G × G => f p.2 * g (p.1 - p.2)) :=
    (hf.comp measurable_snd).stronglyMeasurable.mul
      (hg.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := μ)).measurable

theorem enorm_complexConvolution_le (f g : G → ℂ) (x : G) :
    ‖complexConvolution μ f g x‖ₑ ≤
      ((fun y => ‖f y‖ₑ) ⋆ₗ[μ] (fun y => ‖g y‖ₑ)) x := by
  simpa only [complexConvolution_apply, lconvolution_def, enorm_mul, neg_add_eq_sub] using
    enorm_integral_le_lintegral_enorm (μ := μ) (fun y => f y * g (x - y))

theorem complexConvolution_eLpNorm_one_le {f g : G → ℂ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (complexConvolution μ f g) 1 μ ≤ eLpNorm f 1 μ * eLpNorm g 1 μ := by
  have hc : AEStronglyMeasurable (complexConvolution μ f g) μ :=
    hf.convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  calc
    _ ≤ eLpNorm ((fun y => ‖f y‖ₑ) ⋆ₗ[μ] (fun y => ‖g y‖ₑ)) 1 μ :=
      eLpNorm_mono_enorm_ae hc (Eventually.of_forall fun x => by
        simpa only [enorm_eq_self] using enorm_complexConvolution_le (μ := μ) f g x)
    _ = _ := by
      rw [lconvolution_eLpNorm_one hf.enorm hg.enorm, eLpNorm_enorm f hf, eLpNorm_enorm g hg]

theorem complexConvolution_eLpNorm_two_le {f g : G → ℂ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (complexConvolution μ f g) 2 μ ≤ eLpNorm f 1 μ * eLpNorm g 2 μ := by
  have hc : AEStronglyMeasurable (complexConvolution μ f g) μ :=
    hf.convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  calc
    _ ≤ eLpNorm ((fun y => ‖f y‖ₑ) ⋆ₗ[μ] (fun y => ‖g y‖ₑ)) 2 μ :=
      eLpNorm_mono_enorm_ae hc (Eventually.of_forall fun x => by
        simpa only [enorm_eq_self] using enorm_complexConvolution_le (μ := μ) f g x)
    _ ≤ eLpNorm (fun y => ‖f y‖ₑ) 1 μ * eLpNorm (fun y => ‖g y‖ₑ) 2 μ :=
      lconvolution_eLpNorm_two_le hf.enorm hg.enorm
    _ = _ := by rw [eLpNorm_enorm f hf, eLpNorm_enorm g hg]

theorem complexConvolution_memLp_one {f g : G → ℂ}
    (hf : MemLp f 1 μ) (hg : MemLp g 1 μ) : MemLp (complexConvolution μ f g) 1 μ :=
  (complexConvolution_eLpNorm_one_le hf.aestronglyMeasurable hg.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top hf hg)

theorem complexConvolution_memLp_two {f g : G → ℂ}
    (hf : MemLp f 1 μ) (hg : MemLp g 2 μ) : MemLp (complexConvolution μ f g) 2 μ :=
  (complexConvolution_eLpNorm_two_le hf.aestronglyMeasurable hg.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top hf hg)

end ContinuousFlexibility.Analysis
