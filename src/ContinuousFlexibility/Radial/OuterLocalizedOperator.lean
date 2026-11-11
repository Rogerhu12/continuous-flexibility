import ContinuousFlexibility.Analysis.L2LocalizedKernel
import ContinuousFlexibility.Radial.OuterWholeMeasure
import ContinuousFlexibility.Radial.OuterWholeKernelBounds

/-!
# Actual whole-outer localizers and their same-kernel operator norm

The original smooth partition gives bounded multipliers on the reflected
whole measure. A pointwise bound on their actual kernel controls the norm
of their composition with the already constructed Green operator.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem outer_partition_localizer_abs_le_one {D : ReferenceData}
    (hpart : RadialPartition D) (m : ℕ) (r : ℝ) : |D.localizer m r| ≤ 1 := by
  rw [abs_of_nonneg (hpart.2.1 m r)]
  by_cases hz : D.localizer m r = 0
  · rw [hz]
    exact zero_le_one
  have hcore : r ∈ radialCore D := hpart.2.2.2.1 m (hpart.2.2.1 m hz)
  have hsum := hpart.2.2.2.2.1 r hcore
  exact (hsum.1.le_tsum m (fun k _ => hpart.2.1 k r)).trans_eq hsum.2

theorem outer_localizer_measurable {D : ReferenceData}
    (hpart : RadialPartition D) (right : Bool) (m : ℕ) :
    Measurable (fun x => D.localizer m (outerOutwardRadius right x)) := by
  have hcont : Continuous (outerOutwardRadius right) := by
    cases right
    · exact continuous_neg
    · exact continuous_id
  exact ((hpart.1 m).continuous.comp hcont).measurable

def outerWholeLocalizerMultiplier {D : ReferenceData} (hpart : RadialPartition D)
    (right : Bool) (entry : ℝ) (m : ℕ) :
    OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry :=
  l2BoundedMultiplier (outerWholeMeasure D right entry)
    (outer_localizer_measurable hpart right m).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x =>
      outer_partition_localizer_abs_le_one hpart m (outerOutwardRadius right x)))

def outerWholeLocalizedOperator {D : ReferenceData} (hpart : RadialPartition D)
    (right : Bool) (entry : ℝ) (k m : ℕ)
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry) :
    OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry :=
  (outerWholeLocalizerMultiplier hpart right entry k).comp
    (R.comp (outerWholeLocalizerMultiplier hpart right entry m))

theorem outerWholeLocalizedOperator_kernel {D : ReferenceData}
    (hpart : RadialPartition D) (right : Bool) (entry : ℝ) (k m : ℕ)
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry)
    (K : ℝ → ℝ → ℝ)
    (hR : ∀ f : OuterWholeL2 D right entry,
      (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] fun x =>
        ∫ y, K x y * f y ∂outerWholeMeasure D right entry)
    (f : OuterWholeL2 D right entry) :
    (outerWholeLocalizedOperator hpart right entry k m R f : ℝ → ℝ) =ᵐ[
        outerWholeMeasure D right entry] fun x =>
      ∫ y, (D.localizer k (outerOutwardRadius right x) * K x y *
        D.localizer m (outerOutwardRadius right y)) * f y ∂outerWholeMeasure D right entry :=
  l2Multiplier_comp_kernel (outerWholeMeasure D right entry)
    (outer_localizer_measurable hpart right k).aestronglyMeasurable
    (outer_localizer_measurable hpart right m).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x =>
      outer_partition_localizer_abs_le_one hpart k (outerOutwardRadius right x)))
    (Filter.Eventually.of_forall (fun x =>
      outer_partition_localizer_abs_le_one hpart m (outerOutwardRadius right x))) R K hR f

theorem outerGreenKernel_rows_aestronglyMeasurable (μ : Measure ℝ)
    {a b lam : ℝ} {U V : ℝ → ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioo a b)
    (hU : ContinuousOn U (Ico a b)) (hV : ContinuousOn V (Ico a b)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (outerGreenKernel lam U V x) μ := by
  filter_upwards [hμ] with x hx
  have hmin : ContinuousOn (fun y => U (min x y)) (Ioo a b) :=
    hU.comp (continuous_const.min continuous_id).continuousOn
      (fun y hy => ⟨le_min hx.1.le hy.1.le, (min_le_left _ _).trans_lt hx.2⟩)
  have hmax : ContinuousOn (fun y => V (max x y)) (Ioo a b) :=
    hV.comp (continuous_const.max continuous_id).continuousOn
      (fun y hy => ⟨hx.1.le.trans (le_max_left _ _), max_lt hx.2 hy.2⟩)
  have hrow : ContinuousOn (outerGreenKernel lam U V x) (Ioo a b) :=
    continuousOn_const.mul (hmin.mul hmax)
  have h := hrow.aestronglyMeasurable (μ := μ) measurableSet_Ioo
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at h
  exact h

theorem outerWholeLocalizedOperator_norm_le {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hpart : RadialPartition D)
    (right : Bool) {entry : ℝ} (hentry : entry ∈ radialCore D) (k m : ℕ)
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry)
    (K : ℝ → ℝ → ℝ)
    (hR : ∀ f : OuterWholeL2 D right entry,
      (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] fun x =>
        ∫ y, K x y * f y ∂outerWholeMeasure D right entry)
    (hrow : ∀ᵐ x ∂outerWholeMeasure D right entry,
      AEStronglyMeasurable (K x) (outerWholeMeasure D right entry))
    {B : ℝ} (hB : 0 ≤ B)
    (hpoint : ∀ x ∈ Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)),
      ∀ y ∈ Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)),
      |D.localizer k (outerOutwardRadius right x) * K x y *
        D.localizer m (outerOutwardRadius right y)| ≤ B) :
    ‖outerWholeLocalizedOperator hpart right entry k m R‖ ≤
      (outerWholeMeasure D right entry).real univ * B := by
  let μ := outerWholeMeasure D right entry
  letI : IsFiniteMeasure μ := outerWholeMeasure_isFinite hD right entry
  have hbound : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      |D.localizer k (outerOutwardRadius right x) * K x y *
        D.localizer m (outerOutwardRadius right y)| ≤ B := by
    filter_upwards [outerWholeMeasure_ae_mem hentry] with x hx
    filter_upwards [outerWholeMeasure_ae_mem hentry] with y hy
    exact hpoint x hx y hy
  have h := l2Multiplier_comp_norm_le μ
    (outer_localizer_measurable hpart right k).aestronglyMeasurable
    (outer_localizer_measurable hpart right m).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x =>
      outer_partition_localizer_abs_le_one hpart k (outerOutwardRadius right x)))
    (Filter.Eventually.of_forall (fun x =>
      outer_partition_localizer_abs_le_one hpart m (outerOutwardRadius right x)))
    R K hR hrow hB hbound
  have hmass : (measureUnivNNReal μ : ℝ) = μ.real univ := by
    simpa only [ENNReal.coe_toReal, measureReal_def] using
      congrArg ENNReal.toReal (coe_measureUnivNNReal μ)
  rw [hmass] at h
  exact h

end ContinuousFlexibility.Radial
