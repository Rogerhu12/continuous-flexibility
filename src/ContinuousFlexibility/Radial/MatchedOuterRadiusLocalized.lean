module

public import ContinuousFlexibility.Radial.MatchedRadiusMultipliers
public import ContinuousFlexibility.Radial.MatchedOuterModalCells

/-!
# Actual final-reference cell norms from the original radius kernel

The final localizers are pulled back pointwise by the radius isometry.
This remains valid on the finite core, where the retained order coordinate
can differ from a dilation. Both conclusions concern the supplied
transported operator and supplied vector on all L² sources.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem matchedOuter_radius_localizer_measurable {E : ReferenceData}
    (hE : RadialPartition E) (right : Bool) (μ : Measure ℝ) (κ : ℝ) (m : ℕ) :
    AEStronglyMeasurable
      (fun x => E.localizer m (outerOutwardRadius right (κ * x))) μ := by
  have hc : Continuous (fun x => outerOutwardRadius right (κ * x)) := by
    cases right
    · change Continuous (fun x : ℝ => -(κ * x))
      exact (continuous_const.mul continuous_id).neg
    · change Continuous (fun x : ℝ => κ * x)
      exact continuous_const.mul continuous_id
  exact ((hE.1 m).continuous.comp hc).measurable.aestronglyMeasurable

theorem norm_inverseRadiusOperator_outerCells_le_of_kernel
    {E : ReferenceData} (hE : RadialPartition E) (right : Bool)
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (K : ℝ → ℝ → ℝ)
    (hR : ∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ]
      fun x => ∫ y, K x y * f y ∂μ)
    (hrow : ∀ᵐ x ∂μ, AEStronglyMeasurable (K x) μ)
    (k m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      |E.localizer k (outerOutwardRadius right (κ * x)) * K x y *
        E.localizer m (outerOutwardRadius right (κ * y))| ≤ B) :
    ‖(matchedOuterCell E hE right ν k).comp
      ((inverseRadiusOperator hκ hβ hm R).comp (matchedOuterCell E hE right ν m))‖ ≤
        (measureUnivNNReal μ : ℝ) * B := by
  let φ (i : ℕ) (x : ℝ) := E.localizer i (outerOutwardRadius right (κ * x))
  have hφ (i : ℕ) : AEStronglyMeasurable (φ i) μ :=
    matchedOuter_radius_localizer_measurable hE right μ κ i
  have hφb (i : ℕ) : ∀ᵐ x ∂μ, |φ i x| ≤ 1 :=
    Eventually.of_forall fun x => matchedRadialLocalizer_abs_le_one hE i _
  have hψb (i : ℕ) : ∀ᵐ x ∂ν, |E.localizer i (outerOutwardRadius right x)| ≤ 1 :=
    Eventually.of_forall fun x => matchedRadialLocalizer_abs_le_one hE i _
  have heq := norm_inverseRadiusOperator_multipliers hκ hβ hm (hφ k)
    (matchedOuter_localizer_measurable hE right ν k) (hφb k) (hψb k) EventuallyEq.rfl
    (hφ m) (matchedOuter_localizer_measurable hE right ν m) (hφb m) (hψb m)
    EventuallyEq.rfl R
  change ‖(matchedOuterCell E hE right ν k).comp
      ((inverseRadiusOperator hκ hβ hm R).comp (matchedOuterCell E hE right ν m))‖ =
    ‖(l2BoundedMultiplier μ (hφ k) (hφb k)).comp
      (R.comp (l2BoundedMultiplier μ (hφ m) (hφb m)))‖ at heq
  rw [heq]
  exact l2Multiplier_comp_norm_le μ (hφ k) (hφ m) (hφb k) (hφb m)
    R K hR hrow hB hbound

theorem norm_matchedOuterCell_le_of_radius_value
    {E : ReferenceData} (hE : RadialPartition E) (right : Bool)
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (U : Lp ℝ 2 ν) (V : ℝ → ℝ)
    (hU : (inverseRadiusEquiv hκ hβ hm U : ℝ → ℝ) =ᵐ[μ] V)
    (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ, E.localizer m (outerOutwardRadius right (κ * x)) ≠ 0 →
      |V x| ≤ B) :
    ‖matchedOuterCell E hE right ν m U‖ ≤ sqrt (measureUnivNNReal μ : ℝ) * B := by
  let φ (x : ℝ) := E.localizer m (outerOutwardRadius right (κ * x))
  have hφ : AEStronglyMeasurable φ μ :=
    matchedOuter_radius_localizer_measurable hE right μ κ m
  have hφb : ∀ᵐ x ∂μ, |φ x| ≤ 1 :=
    Eventually.of_forall fun x => matchedRadialLocalizer_abs_le_one hE m _
  have hψb : ∀ᵐ x ∂ν, |E.localizer m (outerOutwardRadius right x)| ≤ 1 :=
    Eventually.of_forall fun x => matchedRadialLocalizer_abs_le_one hE m _
  have heq := norm_inverseRadiusEquiv_multiplier hκ hβ hm hφ
    (matchedOuter_localizer_measurable hE right ν m) hφb hψb EventuallyEq.rfl U
  change ‖matchedOuterCell E hE right ν m U‖ =
    ‖l2BoundedMultiplier μ hφ hφb (inverseRadiusEquiv hκ hβ hm U)‖ at heq
  rw [heq]
  have hbnd : ∀ᵐ x ∂μ,
      ‖l2BoundedMultiplier μ hφ hφb (inverseRadiusEquiv hκ hβ hm U) x‖ ≤ B := by
    filter_upwards [l2BoundedMultiplier_ae μ hφ hφb
      (inverseRadiusEquiv hκ hβ hm U), hU, hbound, hφb] with x hx hUx hb hxφ
    rw [hx, hUx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hz : φ x = 0
    · simpa only [hz, abs_zero, zero_mul] using hB
    · exact (mul_le_mul hxφ (hb hz) (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
  simpa only [Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div] using
    Lp.norm_le_of_ae_bound hB hbnd

end ContinuousFlexibility.Radial
