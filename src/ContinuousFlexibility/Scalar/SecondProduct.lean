import ContinuousFlexibility.Scalar.HeightDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Actual second derivatives of scalar products

The product rule for the first derivative holds on a neighborhood of a
C² point. Differentiating that actual germ gives the second product rule.
These formulas isolate the principal quadratic form of a divergence
operator using test functions that vanish to first order.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The first product rule in any actual coordinate direction. -/
theorem polar_directional_mul {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (u : PolarPoint) :
    fderiv ℝ (fun y => f y * g y) x u =
      fderiv ℝ f x u * g x + f x * fderiv ℝ g x u := by
  simp only [fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The second product rule is obtained from the genuine first-derivative
identity on a neighborhood; the two directions are arbitrary. -/
theorem polar_second_directional_mul {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (u v : PolarPoint) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => f z * g z) y u) x v =
      fderiv ℝ (fun y => fderiv ℝ f y u) x v * g x +
        fderiv ℝ f x u * fderiv ℝ g x v +
        fderiv ℝ f x v * fderiv ℝ g x u +
        f x * fderiv ℝ (fun y => fderiv ℝ g y u) x v := by
  have hfx : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hgx : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hdf : DifferentiableAt ℝ (fun y => fderiv ℝ f y u) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply (differentiableAt_const u)
  have hdg : DifferentiableAt ℝ (fun y => fderiv ℝ g y u) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply (differentiableAt_const u)
  have he :
      (fun y => fderiv ℝ (fun z => f z * g z) y u) =ᶠ[𝓝 x]
        (fun y => fderiv ℝ f y u * g y + f y * fderiv ℝ g y u) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact polar_directional_mul (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num)) u
  have hleft : DifferentiableAt ℝ (fun y => fderiv ℝ f y u * g y) x :=
    hdf.fun_mul hgx
  have hright : DifferentiableAt ℝ (fun y => f y * fderiv ℝ g y u) x :=
    hfx.fun_mul hdg
  rw [he.fderiv_eq, fderiv_fun_add hleft hright]
  simp only [ContinuousLinearMap.add_apply]
  rw [polar_directional_mul hdf hgx, polar_directional_mul hfx hdg]
  ring

/-- A height times a squared scalar function has zero gradient at a zero
of the scalar function. -/
theorem polar_directional_mul_sq_of_zero
    {h f : PolarPoint → ℝ} {x : PolarPoint}
    (hh : DifferentiableAt ℝ h x) (hf : DifferentiableAt ℝ f x)
    (hzero : f x = 0) (u : PolarPoint) :
    fderiv ℝ (fun y => h y * f y ^ 2) x u = 0 := by
  simp only [pow_two]
  have hff : DifferentiableAt ℝ (fun y => f y * f y) x :=
    hf.fun_mul hf
  rw [polar_directional_mul hh hff, polar_directional_mul hf hf, hzero]
  ring

/-- At the same zero its actual Hessian is the rank-one quadratic form
determined by the first derivative of the scalar function. -/
theorem polar_second_directional_mul_sq_of_zero
    {h f : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiffAt ℝ 2 h x) (hf : ContDiffAt ℝ 2 f x)
    (hzero : f x = 0) (u v : PolarPoint) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => h z * f z ^ 2) y u) x v =
      2 * h x * fderiv ℝ f x u * fderiv ℝ f x v := by
  have hfx : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  simp only [pow_two]
  rw [polar_second_directional_mul hh (hf.mul hf)]
  simp only [polar_directional_mul hfx hfx, polar_second_directional_mul hf hf, hzero]
  ring

end ContinuousFlexibility
