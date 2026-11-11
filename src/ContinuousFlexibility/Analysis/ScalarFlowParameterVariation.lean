import ContinuousFlexibility.Analysis.ScalarFlowVariation
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Parameter variation of an actual scalar flow

The ODE and its actual initial value first identify the endpoint with an
integral.  Dominated parameter differentiation is then applied to that
integral.  The last lemma records the simplification of the chain rule
when the velocity's angular derivative vanishes at the base parameter.
No differentiability of the flow endpoint is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- An interior assertion supplies the almost-everywhere premise used by
parameter integration; the right endpoint is a null singleton. -/
theorem ae_uIoc_imp_of_forall_Ioo
    {a b : ℝ} {P : ℝ → Prop} (hab : a ≤ b)
    (hP : ∀ r ∈ Ioo a b, P r) :
    ∀ᵐ r ∂volume, r ∈ uIoc a b → P r := by
  filter_upwards [volume.ae_ne b] with r hr
  intro hri
  have hi : r ∈ Ioc a b := by simpa only [uIoc_of_le hab] using hri
  exact hP r ⟨hi.1, lt_of_le_of_ne hi.2 hr⟩

theorem scalarFlow_eq_initial_add_integral
    {a b θ : ℝ} {Y : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (hab : a ≤ b)
    (hY : ContinuousOn Y (Icc a b)) (hinit : Y a = θ)
    (hODE : ∀ r ∈ Ioo a b, HasDerivAt Y (V r (Y r)) r)
    (hV : IntervalIntegrable (fun r => V r (Y r)) volume a b) :
    Y b = θ + ∫ r in a..b, V r (Y r) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hY hODE hV
  rw [hinit] at h
  linarith only [h]

/-- A dominated derivative of the actual velocity along the actual
trajectories differentiates the actual endpoint.  All differentiability
assumptions on the integrand are almost everywhere in the radial
variable, so no parameter derivative at a turning endpoint is required. -/
theorem hasDerivAt_scalarFlow_endpoint_of_dominated
    {a b θ q0 : ℝ} {U : Set ℝ}
    {Y : ℝ → ℝ → ℝ} {V : ℝ → ℝ → ℝ → ℝ}
    {G : ℝ → ℝ → ℝ} {bound : ℝ → ℝ}
    (hab : a ≤ b) (hU : U ∈ 𝓝 q0)
    (hY : ∀ q ∈ U, ContinuousOn (Y q) (Icc a b))
    (hinit : ∀ q ∈ U, Y q a = θ)
    (hODE : ∀ q ∈ U, ∀ r ∈ Ioo a b,
      HasDerivAt (Y q) (V q r (Y q r)) r)
    (hV : ∀ q ∈ U, IntervalIntegrable (fun r => V q r (Y q r)) volume a b)
    (hG : AEStronglyMeasurable (G q0) (volume.restrict (uIoc a b)))
    (hbound : ∀ᵐ r ∂volume, r ∈ uIoc a b →
      ∀ q ∈ U, ‖G q r‖ ≤ bound r)
    (hboundInt : IntervalIntegrable bound volume a b)
    (hderiv : ∀ᵐ r ∂volume, r ∈ uIoc a b →
      ∀ q ∈ U, HasDerivAt (fun t => V t r (Y t r)) (G q r) q) :
    HasDerivAt (fun q => Y q b) (∫ r in a..b, G q0 r) q0 := by
  have hq0 : q0 ∈ U := mem_of_mem_nhds hU
  have hmeas : ∀ᶠ q in 𝓝 q0,
      AEStronglyMeasurable (fun r => V q r (Y q r)) (volume.restrict (uIoc a b)) := by
    filter_upwards [hU] with q hq
    exact (hV q hq).def'.aestronglyMeasurable
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun q r => V q r (Y q r)) (F' := G) (bound := bound)
    hU hmeas (hV q0 hq0) hG hbound hboundInt hderiv).2
  have heq : (fun q => Y q b) =ᶠ[𝓝 q0]
      (fun q => θ + ∫ r in a..b, V q r (Y q r)) := by
    filter_upwards [hU] with q hq
    exact scalarFlow_eq_initial_add_integral hab (hY q hq) (hinit q hq)
      (hODE q hq) (hV q hq)
  exact (hd.const_add θ).congr_of_eventuallyEq heq

/-- At a parameter where the angular derivative of the velocity vanishes,
the derivative of the composed velocity is just its parameter derivative.
The trajectory may have an arbitrary finite parameter derivative. -/
theorem hasDerivAt_velocity_along_curve_of_zero_angular
    {F : ℝ → ℝ → ℝ} {Y : ℝ → ℝ} {q0 v y : ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v) (q0, Y q0))
    (hY : HasDerivAt Y y q0) :
    HasDerivAt (fun q => F q (Y q)) v q0 := by
  have hinner : HasDerivAt (fun q => (q, Y q)) (1, y) q0 :=
    (hasDerivAt_id q0).prodMk hY
  have h := hF.comp_hasDerivAt q0 hinner
  simpa [Function.comp_def] using h

/-- This version only assumes equality of the angular-free derivative at
almost every radial point; the actual dominated derivative is then
identified by uniqueness. -/
theorem intervalIntegral_parameter_derivative_eq_of_zero_angular
    {a b q0 : ℝ} {V : ℝ → ℝ → ℝ → ℝ} {Y : ℝ → ℝ → ℝ}
    {G f y : ℝ → ℝ}
    (hG : ∀ᵐ r ∂volume, r ∈ uIoc a b →
      HasDerivAt (fun q => V q r (Y q r)) (G r) q0)
    (hV : ∀ᵐ r ∂volume, r ∈ uIoc a b →
      HasFDerivAt (fun p : ℝ × ℝ => V p.1 r p.2)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (f r)) (q0, Y q0 r))
    (hY : ∀ᵐ r ∂volume, r ∈ uIoc a b →
      HasDerivAt (fun q => Y q r) (y r) q0) :
    (∫ r in a..b, G r) = ∫ r in a..b, f r := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hG, hV, hY] with r hg hv hy
  intro hr
  exact (hg hr).unique (hasDerivAt_velocity_along_curve_of_zero_angular (hv hr) (hy hr))

end ContinuousFlexibility.Analysis
