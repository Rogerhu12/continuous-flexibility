module

public import ContinuousFlexibility.Radial.InnerPositiveExtension
public import ContinuousFlexibility.Radial.MorseRadiusODE
public import ContinuousFlexibility.Radial.Gauge

/-!
# The actual radial flux initial-value problem on an inner interval

The reciprocal of the flat reference weight is extended only for the
initial-value construction. Its germ, and the germ of the second flux
coefficient, agree with the physical expressions at every retained point.
Consequently the solution has its actual conormal flux and satisfies the
actual radial Jacobi equation, including both retained endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff

/-- Arbitrary value and conormal-flux initial data produce an actual
homogeneous radial solution. The flux identity holds as a germ at every
point of the closed interval, so differentiating it at an endpoint is
legitimate. -/
theorem exists_innerRadialFlux_initial {A l h B t₀ : ℝ}
    (hA : 0 < A) (hAl : A < l) (hlh : l ≤ h) (hhB : h < B)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hwnonneg : ∀ x, 0 ≤ w x)
    (hwpos : ∀ x ∈ Ioo A B, 0 < w x) (j : ℝ)
    (ht₀ : t₀ ∈ Icc l h) (u₀ v₀ : ℝ) :
    ∃ u v : ℝ → ℝ, ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ v ∧ u t₀ = u₀ ∧ v t₀ = v₀ ∧
      (∀ x ∈ Icc l h, (fun y => w y * deriv u y) =ᶠ[𝓝 x] v) ∧
      ∀ x ∈ Icc l h, radialJacobi (j ^ 2) w u x = 0 := by
  obtain ⟨p, q, hp, hq, hcoeff⟩ :=
    exists_innerRadialFluxCoefficients hA hAl hlh hhB hw hwnonneg hwpos j
  obtain ⟨u, v, hu, hv, hu₀, hv₀, hODE⟩ := exists_smoothFluxSystem hp hq ht₀ u₀ v₀
  have hsub : Icc l h ⊆ Ioo (l - 1) (h + 1) := by
    intro x hx
    exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have hflux (x : ℝ) (hx : x ∈ Icc l h) :
      (fun y => w y * deriv u y) =ᶠ[𝓝 x] v := by
    have hxODE := hsub hx
    have hxAB : x ∈ Ioo A B := ⟨hAl.trans_le hx.1, hx.2.trans_lt hhB⟩
    filter_upwards [(hcoeff x hx).1, Ioo_mem_nhds hxODE.1 hxODE.2,
      Ioo_mem_nhds hxAB.1 hxAB.2] with y hpy hyODE hyAB
    rw [(hODE y hyODE).1.deriv, hpy, ← mul_assoc,
      mul_inv_cancel₀ (hwpos y hyAB).ne', one_mul]
  refine ⟨u, v, hu, hv, hu₀, hv₀, hflux, ?_⟩
  intro x hx
  rw [radialJacobi, (hflux x hx).deriv_eq, (hODE x (hsub hx)).2.deriv,
    (hcoeff x hx).2.eq_of_nhds, sub_self]

/-- The scalar statement retains the actual initial conormal flux
`w(t₀) u'(t₀)`, rather than an auxiliary extended coefficient. -/
theorem exists_innerRadialODE_initial {A l h B t₀ : ℝ}
    (hA : 0 < A) (hAl : A < l) (hlh : l ≤ h) (hhB : h < B)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hwnonneg : ∀ x, 0 ≤ w x)
    (hwpos : ∀ x ∈ Ioo A B, 0 < w x) (j : ℝ)
    (ht₀ : t₀ ∈ Icc l h) (u₀ v₀ : ℝ) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ u t₀ = u₀ ∧ w t₀ * deriv u t₀ = v₀ ∧
      ∀ x ∈ Icc l h, radialJacobi (j ^ 2) w u x = 0 := by
  obtain ⟨u, v, hu, _, hu₀, hv₀, hflux, heq⟩ :=
    exists_innerRadialFlux_initial hA hAl hlh hhB hw hwnonneg hwpos j ht₀ u₀ v₀
  exact ⟨u, hu, hu₀, (hflux t₀ ht₀).eq_of_nhds.trans hv₀, heq⟩

/-- Linear combinations preserve the actual divergence-form radial
operator, including its nonconstant leading coefficient. -/
theorem innerRadialJacobi_linear_combination {w u v : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (a c d x : ℝ) :
    radialJacobi a w (fun y => c * u y + d * v y) x =
      c * radialJacobi a w u x + d * radialJacobi a w v x := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hdv := (contDiff_infty_iff_deriv.mp hv).2
  have hcomb (y : ℝ) :
      HasDerivAt (fun t => c * u t + d * v t) (c * deriv u y + d * deriv v y) y := by
    exact (((hu.differentiable (by simp) y).hasDerivAt.const_mul c).fun_add
      ((hv.differentiable (by simp) y).hasDerivAt.const_mul d))
  have hflux : (fun y => w y * deriv (fun t => c * u t + d * v t) y) =
      (fun y => c * (w y * deriv u y) + d * (w y * deriv v y)) := by
    funext y
    rw [(hcomb y).deriv]
    ring
  have hfluxDeriv :
      HasDerivAt (fun y => c * (w y * deriv u y) + d * (w y * deriv v y))
        (c * deriv (fun y => w y * deriv u y) x +
          d * deriv (fun y => w y * deriv v y) x) x := by
    exact ((((hw.mul hdu).differentiable (by simp) x).hasDerivAt.const_mul c).fun_add
      (((hw.mul hdv).differentiable (by simp) x).hasDerivAt.const_mul d))
  unfold radialJacobi
  rw [hflux, hfluxDeriv.deriv]
  ring

end ContinuousFlexibility.Radial
