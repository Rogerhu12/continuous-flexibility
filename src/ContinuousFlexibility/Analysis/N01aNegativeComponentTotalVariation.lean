import ContinuousFlexibility.Analysis.N01aNegativeComponentVariation
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Total logarithmic variation from the finitely many negative components

On a compact interval inside the annulus, the integral of the absolute
logarithmic derivative is the net logarithmic change plus twice the integral
of its negative part. Each negative-component contribution is bounded by the
full logarithmic drop on that component, even when a component crosses an
endpoint of the compact interval.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

/-- The finite family of actual components meeting a closed radial interval. -/
def n01aNegativeComponentsMeeting {D : ReferenceData} (hD : RadialProfileGeometry D)
    {a b : ℝ} (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) :
    Finset (N01aNegativeComponent D) :=
  (N01aNegativeComponent.finite_inter_Icc hD ha hb).toFinset

@[simp] theorem mem_n01aNegativeComponentsMeeting {D : ReferenceData}
    (hD : RadialProfileGeometry D) {a b : ℝ}
    (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (J : N01aNegativeComponent D) :
    J ∈ n01aNegativeComponentsMeeting hD ha hb ↔ (J.interval ∩ Icc a b).Nonempty := by
  simp only [n01aNegativeComponentsMeeting, Set.Finite.mem_toFinset]

private theorem logDerivative_continuousOn {D : ReferenceData}
    (hD : RadialProfileGeometry D) {a b : ℝ}
    (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) :
    ContinuousOn (fun r => deriv D.w r / D.w r) (Icc a b) := by
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  exact (contDiff_infty_iff_deriv.mp hw).2.continuous.continuousOn.div
    hw.continuous.continuousOn (fun r hr =>
      (hD.2.2.2.2.1 r ⟨ha.1.trans_le hr.1, hr.2.trans_lt hb.2⟩).ne')

/-- The signed logarithmic derivative has the exact endpoint primitive. -/
theorem n01a_integral_logDerivative {D : ReferenceData} (hD : RadialProfileGeometry D)
    {a b : ℝ} (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (hab : a ≤ b) :
    (∫ r in a..b, deriv D.w r / D.w r) = Real.log (D.w b) - Real.log (D.w a) := by
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hp (r : ℝ) (hr : r ∈ Icc a b) : 0 < D.w r :=
    hD.2.2.2.2.1 r ⟨ha.1.trans_le hr.1, hr.2.trans_lt hb.2⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hw.continuous.continuousOn.log (fun r hr => (hp r hr).ne'))
  · intro r hr
    exact (hw.differentiable (by simp) r).hasDerivAt.log
      (hp r (Ioo_subset_Icc_self hr)).ne'
  · exact (logDerivative_continuousOn hD ha hb).intervalIntegrable_of_Icc hab

/-- Absolute variation equals the net change plus twice the negative variation. -/
theorem n01a_totalVariation_eq_log_difference_add_negativePart {D : ReferenceData}
    (hD : RadialProfileGeometry D) {a b : ℝ}
    (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (hab : a ≤ b) :
    (∫ r in a..b, |deriv D.w r / D.w r|) =
      Real.log (D.w b) - Real.log (D.w a) +
        2 * ∫ r in a..b, max (-(deriv D.w r / D.w r)) 0 := by
  have hc := logDerivative_continuousOn hD ha hb
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  have hn := (hc.neg.max continuousOn_const).intervalIntegrable_of_Icc (μ := volume) hab
  have he : (fun r => |deriv D.w r / D.w r|) =
      (fun r => deriv D.w r / D.w r + 2 * max (-(deriv D.w r / D.w r)) 0) := by
    funext r
    by_cases h : 0 ≤ deriv D.w r / D.w r
    · rw [abs_of_nonneg h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · have h' : deriv D.w r / D.w r < 0 := lt_of_not_ge h
      rw [abs_of_neg h', max_eq_left (neg_nonneg.mpr h'.le)]
      ring
  rw [he, intervalIntegral.integral_add hi (hn.const_mul 2),
    intervalIntegral.integral_const_mul, n01a_integral_logDerivative hD ha hb hab]

private def componentDensity {D : ReferenceData} (J : N01aNegativeComponent D) : ℝ → ℝ :=
  J.interval.indicator (fun r => |deriv D.w r / D.w r|)

private theorem componentDensity_nonneg {D : ReferenceData} (J : N01aNegativeComponent D)
    (r : ℝ) : 0 ≤ componentDensity J r := by
  classical
  by_cases hr : r ∈ J.interval
  · rw [componentDensity, Set.indicator_of_mem hr]
    exact abs_nonneg _
  · rw [componentDensity, Set.indicator_of_notMem hr]

private theorem componentDensity_integrable {D : ReferenceData}
    (hD : RadialProfileGeometry D) (J : N01aNegativeComponent D) :
    Integrable (componentDensity J) volume := by
  have hi : IntegrableOn (fun r => |deriv D.w r / D.w r|) J.interval volume :=
    (J.intervalIntegrable_logDerivative hD).abs.1.mono_set Ioo_subset_Ioc_self
  exact hi.integrable_indicator (show MeasurableSet J.interval from measurableSet_Ioo)

private theorem componentDensity_integral {D : ReferenceData}
    (hD : RadialProfileGeometry D) (J : N01aNegativeComponent D) :
    (∫ r, componentDensity J r) = Real.log (D.w J.left) - Real.log (D.w J.right) := by
  rw [componentDensity, integral_indicator (show MeasurableSet J.interval from measurableSet_Ioo)]
  calc
    _ = ∫ r in Ioc J.left J.right, |deriv D.w r / D.w r| :=
      integral_Ioc_eq_integral_Ioo.symm
    _ = ∫ r in J.left..J.right, |deriv D.w r / D.w r| :=
      (intervalIntegral.integral_of_le J.left_lt_right.le).symm
    _ = _ := J.integral_abs_logDerivative hD

private theorem componentDensity_intervalIntegral_le {D : ReferenceData}
    (hD : RadialProfileGeometry D) (J : N01aNegativeComponent D) {a b : ℝ} (hab : a ≤ b) :
    (∫ r in a..b, componentDensity J r) ≤
      Real.log (D.w J.left) - Real.log (D.w J.right) := by
  rw [intervalIntegral.integral_of_le hab, ← componentDensity_integral hD J]
  exact setIntegral_le_integral (componentDensity_integrable hD J)
    (Eventually.of_forall (componentDensity_nonneg J))

/-- Any finite family covering the negative points bounds their integrated negative variation. -/
theorem n01a_negativePart_integral_le_component_drops {D : ReferenceData}
    (hD : RadialProfileGeometry D) {a b : ℝ}
    (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (hab : a ≤ b)
    (S : Finset (N01aNegativeComponent D))
    (hcover : ∀ r ∈ Ioo a b, deriv D.w r < 0 → ∃ J ∈ S, r ∈ J.interval) :
    (∫ r in a..b, max (-(deriv D.w r / D.w r)) 0) ≤
      ∑ J ∈ S, (Real.log (D.w J.left) - Real.log (D.w J.right)) := by
  classical
  have hn := ((logDerivative_continuousOn hD ha hb).neg.max continuousOn_const).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hi (J : N01aNegativeComponent D) :
      IntervalIntegrable (componentDensity J) volume a b :=
    (componentDensity_integrable hD J).intervalIntegrable
  have hsum : IntervalIntegrable (fun r => ∑ J ∈ S, componentDensity J r) volume a b := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum S (fun J _ => hi J)
  have hpoint (r : ℝ) (hr : r ∈ Ioo a b) :
      max (-(deriv D.w r / D.w r)) 0 ≤ ∑ J ∈ S, componentDensity J r := by
    have hp : 0 < D.w r := hD.2.2.2.2.1 r ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩
    by_cases hneg : deriv D.w r < 0
    · obtain ⟨J, hJS, hrJ⟩ := hcover r hr hneg
      have hq : deriv D.w r / D.w r < 0 := div_neg_of_neg_of_pos hneg hp
      have he : max (-(deriv D.w r / D.w r)) 0 = componentDensity J r := by
        rw [max_eq_left (neg_nonneg.mpr hq.le), componentDensity,
          Set.indicator_of_mem hrJ, abs_of_neg hq]
      rw [he]
      exact Finset.single_le_sum (fun K _ => componentDensity_nonneg K r) hJS
    · have hq : 0 ≤ deriv D.w r / D.w r := div_nonneg (le_of_not_gt hneg) hp.le
      rw [max_eq_right (neg_nonpos.mpr hq)]
      exact Finset.sum_nonneg fun J _ => componentDensity_nonneg J r
  calc
    _ ≤ ∫ r in a..b, ∑ J ∈ S, componentDensity J r :=
      intervalIntegral.integral_mono_on_of_le_Ioo hab hn hsum hpoint
    _ = ∑ J ∈ S, ∫ r in a..b, componentDensity J r :=
      intervalIntegral.integral_finsetSum (fun J _ => hi J)
    _ ≤ _ := Finset.sum_le_sum fun J _ => componentDensity_intervalIntegral_le hD J hab

/-- Total variation is controlled by a finite collection of full component drops. -/
theorem n01a_totalVariation_le_component_drops_of_cover {D : ReferenceData}
    (hD : RadialProfileGeometry D) {a b : ℝ}
    (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (hab : a ≤ b)
    (S : Finset (N01aNegativeComponent D))
    (hcover : ∀ r ∈ Ioo a b, deriv D.w r < 0 → ∃ J ∈ S, r ∈ J.interval) :
    (∫ r in a..b, |deriv D.w r / D.w r|) ≤
      Real.log (D.w b) - Real.log (D.w a) +
        2 * ∑ J ∈ S, (Real.log (D.w J.left) - Real.log (D.w J.right)) := by
  rw [n01a_totalVariation_eq_log_difference_add_negativePart hD ha hb hab]
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    (n01a_negativePart_integral_le_component_drops hD ha hb hab S hcover) (by norm_num)) _

/-- The finite family of all intersecting components gives the canonical total-variation bound. -/
theorem n01a_totalVariation_le_component_drops {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hR : RadialReturnMargins D) {a b : ℝ}
    (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (hab : a ≤ b) :
    (∫ r in a..b, |deriv D.w r / D.w r|) ≤
      Real.log (D.w b) - Real.log (D.w a) +
        2 * ∑ J ∈ n01aNegativeComponentsMeeting hD ha hb,
          (Real.log (D.w J.left) - Real.log (D.w J.right)) := by
  apply n01a_totalVariation_le_component_drops_of_cover hD ha hb hab
  intro r hr hneg
  obtain ⟨l, h, hJ, hrJ⟩ := hR.1 r ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩ hneg
  let J : N01aNegativeComponent D := ⟨(l, h), hJ⟩
  refine ⟨J, (mem_n01aNegativeComponentsMeeting hD ha hb J).mpr ?_, hrJ⟩
  exact ⟨r, hrJ, Ioo_subset_Icc_self hr⟩

end ContinuousFlexibility.Statements
