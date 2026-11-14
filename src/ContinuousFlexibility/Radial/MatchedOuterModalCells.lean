module

public import ContinuousFlexibility.Analysis.L2LocalizedKernel
public import ContinuousFlexibility.Radial.MatchedModeLocalization
public import ContinuousFlexibility.Radial.OuterDeepDirichletKernel
public import ContinuousFlexibility.Radial.OuterWholeMeasure

/-!
# The specified modal localizers on the actual outward Hilbert space

These are the original localizers composed with the physical reflection.
The norm statements retain the supplied continuous operator and supplied
L2 vector. The integral estimate is the existing all-source kernel
theorem; no substitute inverse is constructed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem matchedOuter_localizer_measurable {D : ReferenceData}
    (hP : RadialPartition D) (right : Bool) (μ : Measure ℝ) (m : ℕ) :
    AEStronglyMeasurable (fun x => D.localizer m (outerOutwardRadius right x)) μ :=
  ((hP.1 m).continuous.measurable.comp
    (measurableEmbedding_outerOutwardRadius right).measurable).aestronglyMeasurable

def matchedOuterCell (D : ReferenceData) (hP : RadialPartition D)
    (right : Bool) (μ : Measure ℝ) (m : ℕ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  l2BoundedMultiplier μ (matchedOuter_localizer_measurable hP right μ m)
    (Eventually.of_forall fun x =>
      matchedRadialLocalizer_abs_le_one hP m (outerOutwardRadius right x))

theorem matchedOuterCell_ae (D : ReferenceData) (hP : RadialPartition D)
    (right : Bool) (μ : Measure ℝ) (m : ℕ) (u : Lp ℝ 2 μ) :
    (matchedOuterCell D hP right μ m u : ℝ → ℝ) =ᵐ[μ]
      fun x => D.localizer m (outerOutwardRadius right x) * u x :=
  l2BoundedMultiplier_ae μ _ _ u

theorem matchedOuterCell_comp_norm_le_of_kernel {D : ReferenceData}
    (hP : RadialPartition D) (right : Bool) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (κ : ℝ → ℝ → ℝ)
    (hR : ∀ f : Lp ℝ 2 μ,
      (R f : ℝ → ℝ) =ᵐ[μ] fun x => ∫ y, κ x y * f y ∂μ)
    (hrow : ∀ᵐ x ∂μ, AEStronglyMeasurable (κ x) μ)
    (k m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      D.localizer k (outerOutwardRadius right x) ≠ 0 →
      D.localizer m (outerOutwardRadius right y) ≠ 0 → |κ x y| ≤ B) :
    ‖(matchedOuterCell D hP right μ k).comp
      (R.comp (matchedOuterCell D hP right μ m))‖ ≤
        (measureUnivNNReal μ : ℝ) * B := by
  apply l2Multiplier_comp_norm_le μ
    (matchedOuter_localizer_measurable hP right μ k)
    (matchedOuter_localizer_measurable hP right μ m)
    (Eventually.of_forall fun x =>
      matchedRadialLocalizer_abs_le_one hP k (outerOutwardRadius right x))
    (Eventually.of_forall fun x =>
      matchedRadialLocalizer_abs_le_one hP m (outerOutwardRadius right x))
    R κ hR hrow hB
  filter_upwards [hbound] with x hx
  filter_upwards [hx] with y hxy
  by_cases hk : D.localizer k (outerOutwardRadius right x) = 0
  · simpa only [hk, zero_mul, abs_zero] using hB
  by_cases hm : D.localizer m (outerOutwardRadius right y) = 0
  · simpa only [hm, mul_zero, abs_zero] using hB
  rw [abs_mul, abs_mul]
  exact (mul_le_mul
    (mul_le_mul (matchedRadialLocalizer_abs_le_one hP k (outerOutwardRadius right x))
      (hxy hk hm) (abs_nonneg _) zero_le_one)
    (matchedRadialLocalizer_abs_le_one hP m (outerOutwardRadius right y))
    (abs_nonneg _) (by simpa only [one_mul] using hB)).trans_eq (by ring)

theorem matchedOuterCell_norm_le_of_value {D : ReferenceData}
    (hP : RadialPartition D) (right : Bool) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (U : Lp ℝ 2 μ) (f : ℝ → ℝ) (hU : (U : ℝ → ℝ) =ᵐ[μ] f)
    (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ, D.localizer m (outerOutwardRadius right x) ≠ 0 → |f x| ≤ B) :
    ‖matchedOuterCell D hP right μ m U‖ ≤
      sqrt (measureUnivNNReal μ : ℝ) * B := by
  have hpoint : ∀ᵐ x ∂μ, ‖matchedOuterCell D hP right μ m U x‖ ≤ B := by
    filter_upwards [matchedOuterCell_ae D hP right μ m U, hU, hbound] with x hx hUx hxb
    rw [hx, hUx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hθ : D.localizer m (outerOutwardRadius right x) = 0
    · simpa only [hθ, abs_zero, zero_mul] using hB
    · exact (mul_le_mul (matchedRadialLocalizer_abs_le_one hP m (outerOutwardRadius right x))
        (hxb hθ) (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
  simpa only [Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div] using
    Lp.norm_le_of_ae_bound hB hpoint

/-- The row measurability used above comes from the actual Dirichlet
and natural solutions, independently of any asserted operator norm. -/
theorem matchedOuter_actual_tail_row_memLp
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
    {entrance η K : ℝ}
    (hD : IsAccumulatingProfile D) (hentry : 0 < entrance)
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    {x : ℝ} (hx : x ∈ Ico (outerOutwardRadius right entrance)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    MemLp (fun y => F.Q (min x y) * F.P (max x y)) 2
      (outerWholeMeasure D right entrance) := by
  have hgeom : RadialProfileGeometry D := by obtain ⟨C, hC⟩ := hD; exact hC.1
  have hc := outerTail_outward_log_mem hgeom right hentry
    (show x ∈ Ico (outerTailSign right * entrance)
      (outerTailSign right * tailPhysicalEndpoint D right) from
      by simpa only [outerOutwardRadius_eq_sign] using hx)
  let t := tailPhysicalLog right (outerTailSign right * x)
  have hxt : outerOutwardLogRadius right t = x := by
    change outerOutwardRadius right
      (tailPhysicalRadius right (tailPhysicalLog right (outerTailSign right * x))) = x
    rw [tailPhysicalRadius_log right hc.1, outerOutwardRadius_eq_sign,
      ← mul_assoc, outerTailSign_mul_self, one_mul]
  have hr := outerOutwardDirichletKernel_row_memLp hD hphysical F.logQ F.logP t
    (F.logDirichletRow_memLp hT hc.2)
  rw [hxt] at hr
  have hm : outerWholeMeasure D right entrance =
      outerOutwardTailMeasure D
        (morsePhysicalDeepTail M D right j start entrance η K) right := by
    rw [← outerWholeMeasure_tail]
    change outerWholeMeasure D right entrance =
      outerWholeMeasure D right (tailPhysicalRadius right (tailPhysicalLog right entrance))
    rw [tailPhysicalRadius_log right hentry]
  rw [hm]
  exact hr

end ContinuousFlexibility.Radial
