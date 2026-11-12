import ContinuousFlexibility.Analysis.N05ReferenceZeroRemainder
import ContinuousFlexibility.Analysis.N05ReferenceCutoffChange
import ContinuousFlexibility.Radial.AngularMeanL2
import ContinuousFlexibility.Radial.R11bWeakNormalTensor

/-!
# The normal jet of the prescribed physical cutoff

The actual cutoff conditions already put its derivative in a compact radial
subset of the physical core. Its derivative therefore belongs to every
output cell weight. The weak normal derivative below uses the prescribed
cutoff itself, so changing the output remainder also changes its normal jet
by the derivative of that same cutoff.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Analysis

theorem n05_leftCutoff_deriv_compact {D : ReferenceData}
    {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) :
    HasCompactRadialSupport D (fun p => deriv χ p.1) := by
  obtain ⟨J, hJ, hJcore, _, hzero⟩ := hχ.2.2
  exact ⟨J, hJ, hJcore, fun r hr _ => hzero r hr⟩

theorem n05_leftCutoff_deriv_contDiff {D : ReferenceData}
    {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) :
    ContDiff ℝ ∞ (fun p : PolarPoint => deriv χ p.1) :=
  (contDiff_infty_iff_deriv.mp hχ.1).2.comp contDiff_fst

theorem n05_leftCutoff_deriv_periodic {χ : ℝ → ℝ} (a : ℝ) :
    Function.Periodic (fun p : PolarPoint => deriv χ p.1) (0, a) := by
  intro p
  change deriv χ (p.1 + 0) = deriv χ p.1
  rw [add_zero]

theorem n05_leftCutoff_deriv_test {D : ReferenceData}
    {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) :
    RadialTest D (fun p => deriv χ p.1) :=
  ⟨n05_leftCutoff_deriv_contDiff hχ,
    n05_leftCutoff_deriv_periodic (2 * Real.pi), n05_leftCutoff_deriv_compact hχ⟩

theorem n05_leftCutoff_deriv_output_weights {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {χ : ℝ → ℝ} (hχ : CutoffConditions D χ)
    (γ M : ℝ) :
    RadialCellIntegrable D (fun p => deriv χ p.1) ∧
      Summable (outputCellSquare D γ M (fun p => deriv χ p.1)) := by
  obtain ⟨J, hJ, hJcore, hzero⟩ := n05_leftCutoff_deriv_compact hχ
  exact r11b_compact_output_cell_summable hD hJ hJcore
    (n05_leftCutoff_deriv_contDiff hχ).continuous
    (fun r _ hr => hzero r hr) γ M

theorem n05_leftCutoff_deriv_outputRealization {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {χ : ℝ → ℝ} (hχ : CutoffConditions D χ)
    (γ M : ℝ) :
    OutputRealization D γ M 0 ((fun p => deriv χ p.1), 0) := by
  obtain ⟨hi, hs⟩ := n05_leftCutoff_deriv_output_weights hD hχ γ M
  refine ⟨?_, ?_, n05_leftCutoff_deriv_periodic Real.pi, fun _ _ => rfl⟩
  · simpa only [n05_outputRemainder_zero] using hi
  · simpa only [n05_outputRemainder_zero] using hs

theorem n05_leftCutoff_weakNormalDerivative {D : ReferenceData}
    (hab : D.a < D.b) {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) :
    WeakNormalDerivative D (fun p => χ p.1) (fun p => deriv χ p.1) := by
  have hd : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ.1).2
  have hw := r11b_weakNormalDerivative_tensor (D := D) hab
    (c := χ) (d := deriv χ) (e := fun _ => (1 : ℝ))
    (interval_memLp_of_continuous hχ.1.continuous)
    (interval_memLp_of_continuous hd.continuous)
    (angularInterval_memLp_of_continuous continuous_const)
    (fun r _ => (hχ.1.differentiable (by simp) r).hasDerivAt)
    hd.continuous.continuousOn
  simpa only [mul_one] using hw

/-- The actual first normal jet of the remainder with the physical cutoff. -/
theorem n05_weakNormalDerivative_sub_leftCutoff {D : ReferenceData}
    (hab : D.a < D.b) {χ : ℝ → ℝ} (hχ : CutoffConditions D χ)
    {u ur : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hur : MemLp ur 2 (radialPhysicalMeasure D))
    (hweak : WeakNormalDerivative D u ur) (a : ℝ) :
    WeakNormalDerivative D (fun p => u p - a * χ p.1)
      (fun p => ur p - a * deriv χ p.1) := by
  have hc : MemLp (fun p : PolarPoint => χ p.1) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (hχ.1.continuous.comp continuous_fst)
  have hd : MemLp (fun p : PolarPoint => deriv χ p.1) 2
      (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (n05_leftCutoff_deriv_contDiff hχ).continuous
  intro φ hφ
  have hφLp : MemLp φ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hφ.1.continuous
  have hφrLp : MemLp (radialPartial φ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_radialTest_radialPartial hφ).1.continuous
  have hw := hweak φ hφ
  have hcut := n05_leftCutoff_weakNormalDerivative hab hχ φ hφ
  rw [r11b_integral_angularMean_mul_eq hab.le hu hφrLp,
    r11b_integral_angularMean_mul_eq hab.le hur hφLp] at hw
  rw [r11b_integral_angularMean_mul_eq hab.le hc hφrLp,
    r11b_integral_angularMean_mul_eq hab.le hd hφLp] at hcut
  have hw' : (∫ p, u p * radialPartial φ p ∂radialPhysicalMeasure D) =
      -(∫ p, ur p * φ p ∂radialPhysicalMeasure D) := by
    apply mul_left_cancel₀ (inv_ne_zero (by positivity : (2 * Real.pi) ≠ 0))
    simpa only [mul_neg] using hw
  have hc' : (∫ p, χ p.1 * radialPartial φ p ∂radialPhysicalMeasure D) =
      -(∫ p, deriv χ p.1 * φ p ∂radialPhysicalMeasure D) := by
    apply mul_left_cancel₀ (inv_ne_zero (by positivity : (2 * Real.pi) ≠ 0))
    simpa only [mul_neg] using hcut
  rw [r11b_integral_angularMean_mul_eq hab.le (hu.sub (hc.const_mul a)) hφrLp,
    r11b_integral_angularMean_mul_eq hab.le (hur.sub (hd.const_mul a)) hφLp]
  simp_rw [sub_mul, mul_assoc]
  have huφrInt : Integrable (fun p => u p * radialPartial φ p) (radialPhysicalMeasure D) :=
    hu.integrable_mul hφrLp
  have hcφrInt : Integrable (fun p => a * (χ p.1 * radialPartial φ p))
      (radialPhysicalMeasure D) :=
    (hc.integrable_mul hφrLp).const_mul a
  have hurφInt : Integrable (fun p => ur p * φ p) (radialPhysicalMeasure D) :=
    hur.integrable_mul hφLp
  have hdφInt : Integrable (fun p => a * (deriv χ p.1 * φ p)) (radialPhysicalMeasure D) :=
    (hd.integrable_mul hφLp).const_mul a
  rw [integral_sub huφrInt hcφrInt, integral_sub hurφInt hdφInt,
    integral_const_mul, integral_const_mul, hw', hc']
  ring

end ContinuousFlexibility.Statements
