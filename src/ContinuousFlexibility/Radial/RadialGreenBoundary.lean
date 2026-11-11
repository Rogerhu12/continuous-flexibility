import ContinuousFlexibility.Radial.OuterGreenKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Green's identity for the radial Jacobi expression

This is the regular-interval integration identity used for the cut traces.
The derivative calculation keeps the divergence form, so that the
potential cancels before any integration or endpoint condition is used.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

/-- The general Wronskian identity, without a homogeneous-equation hypothesis. -/
theorem hasDerivAt_radialWronskian_general {J r : ℝ} {w u v : ℝ → ℝ}
    (hw : DifferentiableAt ℝ w r)
    (hu : DifferentiableAt ℝ u r) (hdu : DifferentiableAt ℝ (deriv u) r)
    (hv : DifferentiableAt ℝ v r) (hdv : DifferentiableAt ℝ (deriv v) r) :
    HasDerivAt (radialWronskian w u v)
      (u r * radialJacobi J w v r - v r * radialJacobi J w u r) r := by
  have hup := (hw.mul hdu).hasDerivAt
  have hvp := (hw.mul hdv).hasDerivAt
  have h := (hu.hasDerivAt.mul hvp).sub (hv.hasDerivAt.mul hup)
  have heq : radialWronskian w u v =
      fun t => u t * (w t * deriv v t) - v t * (w t * deriv u t) := by
    funext t
    unfold radialWronskian
    ring
  rw [heq]
  exact h.congr_deriv (by unfold radialJacobi; ring)

/-- Green's identity on a regular closed interval. The hypotheses are
stated at the actual interval, rather than as global smoothness. -/
theorem integral_radialJacobi_green {a b J : ℝ} {w u v : ℝ → ℝ}
    (hreg : ∀ r ∈ uIcc a b,
      DifferentiableAt ℝ w r ∧ DifferentiableAt ℝ u r ∧
      DifferentiableAt ℝ (deriv u) r ∧ DifferentiableAt ℝ v r ∧
      DifferentiableAt ℝ (deriv v) r)
    (hint : IntervalIntegrable
      (fun r => u r * radialJacobi J w v r - v r * radialJacobi J w u r)
      volume a b) :
    (∫ r in a..b,
      u r * radialJacobi J w v r - v r * radialJacobi J w u r) =
        radialWronskian w u v b - radialWronskian w u v a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro r hr
  obtain ⟨hw, hu, hdu, hv, hdv⟩ := hreg r hr
  exact hasDerivAt_radialWronskian_general hw hu hdu hv hdv

/-- At a Dirichlet endpoint, the Wronskian depends only on the other
function's value and on the Dirichlet function's flux. -/
theorem radialWronskian_of_dirichlet
    (w u v : ℝ → ℝ) (r : ℝ) (hu : u r = 0) :
    radialWronskian w v u r = v r * (w r * deriv u r) := by
  simp only [radialWronskian, hu, mul_zero, sub_zero]
  ring

/-- The alternating boundary form vanishes on a separated real line.
The normalization allows either component of the line to vanish. -/
theorem matching_boundary_form_eq_zero
    {a b x z y t : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (h1 : a * x + b * z = 0) (h2 : a * y + b * t = 0) :
    x * t - z * y = 0 := by
  have ha : a * (x * t - z * y) = 0 := by
    linear_combination t * h1 - z * h2
  have hb : b * (x * t - z * y) = 0 := by
    linear_combination x * h2 - y * h1
  linear_combination a * ha + b * hb - (x * t - z * y) * hab


/-- Green's identity with absolutely continuous fluxes. This is the form
needed for L2 sources: no second classical derivative of the inhomogeneous
solution is assumed, and endpoint fluxes are the continuous flux values. -/
theorem integral_green_of_absolutelyContinuous_flux
    {a b : ℝ} {w u v p q f g : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b)
    (hv : AbsolutelyContinuousOnInterval v a b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hpu : ∀ᵐ x ∂volume, x ∈ uIcc a b → p x = w x * deriv u x)
    (hqv : ∀ᵐ x ∂volume, x ∈ uIcc a b → q x = w x * deriv v x)
    (hpf : ∀ᵐ x ∂volume, x ∈ uIcc a b → deriv p x = f x)
    (hqg : ∀ᵐ x ∂volume, x ∈ uIcc a b → deriv q x = g x) :
    (∫ x in a..b, u x * g x - v x * f x) =
      (u b * q b - v b * p b) - (u a * q a - v a * p a) := by
  let W : ℝ → ℝ := fun x => u x * q x - v x * p x
  have hW : AbsolutelyContinuousOnInterval W a b :=
    (hu.fun_mul hq).fun_sub (hv.fun_mul hp)
  change (∫ x in a..b, u x * g x - v x * f x) = W b - W a
  rw [← hW.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hu.ae_differentiableAt, hv.ae_differentiableAt,
    hp.ae_differentiableAt, hq.ae_differentiableAt, hpu, hqv, hpf, hqg]
    with x hux hvx hpx hqx hpux hqvx hpfx hqgx hxi
  have hx : x ∈ uIcc a b := uIoc_subset_uIcc hxi
  have hd := ((hux hx).hasDerivAt.mul (hqx hx).hasDerivAt).sub
    ((hvx hx).hasDerivAt.mul (hpx hx).hasDerivAt)
  change u x * g x - v x * f x =
    deriv (fun t => u t * q t - v t * p t) x
  rw [hd.deriv, hpux hx, hqvx hx, hpfx hx, hqgx hx]
  ring

end ContinuousFlexibility.Radial
