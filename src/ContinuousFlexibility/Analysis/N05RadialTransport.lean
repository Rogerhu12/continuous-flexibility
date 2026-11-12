import ContinuousFlexibility.Geometry.GraphSurfaceGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact radial transport for actual planar functions

For a real primitive A with derivative b, the actual equation
N_r = b N_theta says that N(t, theta + A(x) - A(t)) has derivative zero.
The fundamental theorem of calculus gives the endpoint formula on the
whole closed strip, requiring only continuity at its physical endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped Topology

/-- A real function continuous on a closed interval and with zero actual
derivative in the interior has the same value at all points of that interval. -/
theorem n05_closed_interval_zero_derivative
    {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : f x = f y := by
  have hleft (t : ℝ) (ht : t ∈ Icc a b) : f t = f a := by
    have hsub : Icc a t ⊆ Icc a b := fun _ hz => ⟨hz.1, hz.2.trans ht.2⟩
    have hzero := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f' := fun _ : ℝ => (0 : ℝ)) ht.1 (hf.mono hsub)
      (fun z hz => hd z ⟨hz.1, hz.2.trans_le ht.2⟩)
      (IntervalIntegrable.zero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a t)
    have hdiff : f t - f a = 0 := by
      simpa only [intervalIntegral.integral_zero] using hzero.symm
    exact sub_eq_zero.mp hdiff
  exact (hleft x hx).trans (hleft y hy).symm

/-- Transport by a genuine radial primitive. The equation is verified using
the actual Frechet differential and holds up to either endpoint. -/
theorem n05_radial_transport
    {N : PolarPoint → ℝ} {A speed : ℝ → ℝ} {a b : ℝ}
    (hN : ContinuousOn N (Icc a b ×ˢ univ))
    (hNd : ∀ p : PolarPoint, p.1 ∈ Ioo a b → DifferentiableAt ℝ N p)
    (hA : ContinuousOn A (Icc a b))
    (hAd : ∀ t ∈ Ioo a b, HasDerivAt A (speed t) t)
    (hPDE : ∀ p : PolarPoint, p.1 ∈ Ioo a b →
      radialPartial N p = speed p.1 * angularPartial N p)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (θ : ℝ) :
    N (x, θ) = N (y, θ + A x - A y) := by
  let F : ℝ → ℝ := fun t => N (t, θ + A x - A t)
  have hcurve : ContinuousOn (fun t : ℝ => (t, θ + A x - A t)) (Icc a b) :=
    continuousOn_id.prodMk (continuousOn_const.sub hA)
  have hF : ContinuousOn F (Icc a b) :=
    hN.comp hcurve (fun t ht => ⟨ht, mem_univ _⟩)
  have hFd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt F 0 t := by
    have hcurveD : HasDerivAt (fun u : ℝ => (u, θ + A x - A u))
        (1, -speed t) t := by
      exact (hasDerivAt_id' t).prodMk
        (HasDerivAt.const_sub (θ + A x) (hAd t ht))
    have hcomp := (hNd (t, θ + A x - A t) ht).hasFDerivAt.comp_hasDerivAt t hcurveD
    have hvalue : fderiv ℝ N (t, θ + A x - A t) (1, -speed t) = 0 := by
      rw [height_fderiv_coordinates, hPDE (t, θ + A x - A t) ht]
      ring
    simpa only [F, Function.comp_def] using hcomp.congr_deriv hvalue
  have heq := n05_closed_interval_zero_derivative hF hFd hx hy
  simpa only [F, add_sub_cancel_right] using heq

end ContinuousFlexibility.Statements
