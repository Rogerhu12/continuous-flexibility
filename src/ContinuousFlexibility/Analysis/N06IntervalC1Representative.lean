import ContinuousFlexibility.Analysis.WeightedEndpointTrace
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A genuine global C1 representative of a bounded-jet interval function

The actual first derivative is extended continuously using its integrable
second derivative. Integrating that extension and matching one constant
constructs the global C1 function. No totalized endpoint value is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- Interior smoothness and one finite bound for the actual second
derivative construct a global C1 representative on the open interval. -/
theorem n06_exists_contDiff_one_representative_of_bounded_second_deriv
    {a b : ℝ} {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    {M : ℝ} (hbound : ∀ x ∈ Ioo a b, |deriv (deriv f) x| ≤ M) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 1 g ∧ EqOn f g (Ioo a b) := by
  have hfirst : DifferentiableOn ℝ (deriv f) (Ioo a b) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      differentiableOn_iteratedDeriv_Ioo hf 1
  have hsecond : ContinuousOn (deriv (deriv f)) (Ioo a b) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (differentiableOn_iteratedDeriv_Ioo hf 2).continuousOn
  have hint : IntegrableOn (deriv (deriv f)) (Ioo a b) := by
    apply (integrableOn_const (C := M) (μ := volume)
      (s := Ioo a b) measure_Ioo_lt_top.ne).mono'
      (hsecond.aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hbound x hx
  obtain ⟨v, hv, hfv⟩ := exists_continuous_extension_of_integrable_deriv
    (fun x hx => ((hfirst x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt)
    hsecond hint
  let J : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, v t
  have hJd (x : ℝ) : HasDerivAt J (v x) x :=
    intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 x)
      hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
  have hJformula : deriv J = v := funext (fun x => (hJd x).deriv)
  have hJ : ContDiff ℝ 1 J := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (hJd x).differentiableAt, ?_⟩
    rw [hJformula]
    exact hv
  have hfd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt f (deriv f x) x :=
    ((hf.differentiableOn (by simp) x hx).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hdiff : DifferentiableOn ℝ (fun x => f x - J x) (Ioo a b) :=
    fun x hx => ((hfd x hx).sub (hJd x)).differentiableAt.differentiableWithinAt
  have hzero (x : ℝ) (hx : x ∈ Ioo a b) : deriv (fun y => f y - J y) x = 0 := by
    have he := ((hfd x hx).sub (hJd x)).deriv
    simpa only [Pi.sub_def, hfv hx, sub_self] using he
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    isPreconnected_Ioo hdiff hzero
  refine ⟨fun x => J x + c, hJ.add contDiff_const, fun x hx => ?_⟩
  have he := hc x hx
  change f x - J x = c at he
  linarith only [he]

end ContinuousFlexibility.Analysis
