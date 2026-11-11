import ContinuousFlexibility.Radial.PositiveBufferFullForm

/-!
# Restricting the physical field to the retained interval

The scalar border coordinate is retained. The field coordinate is the actual
Lebesgue L² restriction followed by zero extension.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology

def positiveBufferRetainedProjection (l h : ℝ) :
    (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ) :=
  ((bufferL2IndicatorCLM (Ioo l h) measurableSet_Ioo).comp
    (ContinuousLinearMap.fst ℝ RadialL2 ℝ)).prod
    (ContinuousLinearMap.snd ℝ RadialL2 ℝ)

@[simp] theorem positiveBufferRetainedProjection_apply (l h : ℝ) (F : RadialL2 × ℝ) :
    positiveBufferRetainedProjection l h F =
      (bufferL2Indicator (Ioo l h) measurableSet_Ioo F.1, F.2) := by
  simp only [positiveBufferRetainedProjection, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.fst_apply,
    ContinuousLinearMap.snd_apply, bufferL2IndicatorCLM_apply]

theorem positiveBufferRetainedProjection_norm_le (l h : ℝ) (F : RadialL2 × ℝ) :
    ‖positiveBufferRetainedProjection l h F‖ ≤ ‖F‖ := by
  rw [positiveBufferRetainedProjection_apply, Prod.norm_def, Prod.norm_def]
  exact max_le_max (bufferL2Indicator_norm_le _ _ _) le_rfl

theorem bufferL2Indicator_eq_self_of_supported (s : Set ℝ) (hs : MeasurableSet s)
    (u : RadialL2) (hu : (u : ℝ → ℝ) =ᵐ[volume.restrict sᶜ] (fun _ => 0)) :
    bufferL2Indicator s hs u = u := by
  apply Lp.ext
  have hz := (ae_restrict_iff' hs.compl).mp hu
  filter_upwards [bufferL2Indicator_coeFn s hs u, hz] with x hx hzero
  rw [hx]
  by_cases hxs : x ∈ s
  · exact Set.indicator_of_mem hxs _
  · rw [Set.indicator_of_notMem hxs, hzero hxs]

theorem positiveBufferRetainedProjection_eq_self (l h : ℝ) (F : RadialL2 × ℝ)
    (hF : (F.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo l h)ᶜ)] (fun _ => 0)) :
    positiveBufferRetainedProjection l h F = F := by
  rw [positiveBufferRetainedProjection_apply,
    bufferL2Indicator_eq_self_of_supported _ _ _ hF]

theorem positiveBufferRetainedProjection_supported (l h : ℝ) (F : RadialL2 × ℝ) :
    ((positiveBufferRetainedProjection l h F).1 : ℝ → ℝ) =ᵐ[
      volume.restrict ((Ioo l h)ᶜ)] (fun _ => 0) := by
  rw [positiveBufferRetainedProjection_apply]
  filter_upwards [ae_restrict_of_ae
    (bufferL2Indicator_coeFn (Ioo l h) measurableSet_Ioo F.1),
    ae_restrict_mem measurableSet_Ioo.compl] with x hx hout
  rw [hx, Set.indicator_of_notMem hout]

end ContinuousFlexibility.Radial
