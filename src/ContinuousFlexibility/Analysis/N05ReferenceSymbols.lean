module

public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Extracting the actual principal symbol in reference coordinates

The product identity below uses the genuine Frechet partial derivatives.
Centered quadratic tests remove all lower-order terms of a conjugated
divergence operator. Thus a coordinate identity on smooth functions
determines the transported principal form; no independent coordinate jets
or assumed principal-symbol transformation are introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The principal bilinear form evaluated on two actual differentials. -/
def n05PrincipalPair (L : SymmetricCoefficients)
    (f g : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  L.a x * radialPartial f x * radialPartial g x +
    L.b x * (radialPartial f x * angularPartial g x +
      angularPartial f x * radialPartial g x) +
    L.c x * angularPartial f x * angularPartial g x

private theorem n05_eventually_differentiable
    {f : PolarPoint → ℝ} {x : PolarPoint} (hf : ContDiffAt ℝ ∞ f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
  have h1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  filter_upwards [h1.eventually (by norm_num)] with y hy
  exact hy.differentiableAt one_ne_zero

/-- The exact product rule for the physical symmetric divergence operator. -/
theorem n05_divergenceOperator_mul
    {L : SymmetricCoefficients} {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ L.a x) (hB : ContDiffAt ℝ ∞ L.b x)
    (hC : ContDiffAt ℝ ∞ L.c x)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    divergenceOperator L (fun y => f y * g y) x =
      f x * divergenceOperator L g x + g x * divergenceOperator L f x +
        2 * n05PrincipalPair L f g x := by
  have df := hf.differentiableAt (by simp)
  have dg := hg.differentiableAt (by simp)
  have dNf := (contDiffAt_symmetricNormalFlux hA hB hf).differentiableAt (by simp)
  have dNg := (contDiffAt_symmetricNormalFlux hA hB hg).differentiableAt (by simp)
  have dTf := (contDiffAt_symmetricAngularFlux hB hC hf).differentiableAt (by simp)
  have dTg := (contDiffAt_symmetricAngularFlux hB hC hg).differentiableAt (by simp)
  have hN :
      symmetricNormalFlux L.a L.b (fun y => f y * g y) =ᶠ[𝓝 x]
        (fun y => f y * symmetricNormalFlux L.a L.b g y +
          g y * symmetricNormalFlux L.a L.b f y) := by
    filter_upwards [n05_eventually_differentiable hf,
      n05_eventually_differentiable hg] with y hfy hgy
    simp only [symmetricNormalFlux, radialPartial_mul hfy hgy,
      angularPartial_mul hfy hgy]
    ring
  have hT :
      symmetricAngularFlux L.b L.c (fun y => f y * g y) =ᶠ[𝓝 x]
        (fun y => f y * symmetricAngularFlux L.b L.c g y +
          g y * symmetricAngularFlux L.b L.c f y) := by
    filter_upwards [n05_eventually_differentiable hf,
      n05_eventually_differentiable hg] with y hfy hgy
    simp only [symmetricAngularFlux, radialPartial_mul hfy hgy,
      angularPartial_mul hfy hgy]
    ring
  have hNr := congrArg (fun F : PolarPoint →L[ℝ] ℝ => F (1, 0))
    (hN.fderiv_eq (𝕜 := ℝ))
  have hTt := congrArg (fun F : PolarPoint →L[ℝ] ℝ => F (0, 1))
    (hT.fderiv_eq (𝕜 := ℝ))
  change radialPartial (symmetricNormalFlux L.a L.b (fun y => f y * g y)) x =
    radialPartial (fun y => f y * symmetricNormalFlux L.a L.b g y +
      g y * symmetricNormalFlux L.a L.b f y) x at hNr
  change angularPartial (symmetricAngularFlux L.b L.c (fun y => f y * g y)) x =
    angularPartial (fun y => f y * symmetricAngularFlux L.b L.c g y +
      g y * symmetricAngularFlux L.b L.c f y) x at hTt
  change symmetricDivergence L.a L.b L.c (fun y => f y * g y) x =
    f x * symmetricDivergence L.a L.b L.c g x +
      g x * symmetricDivergence L.a L.b L.c f x +
        2 * n05PrincipalPair L f g x
  unfold symmetricDivergence
  have hNadd := radialPartial_add (df.mul dNg) (dg.mul dNf)
  have hTadd := angularPartial_add (df.mul dTg) (dg.mul dTf)
  simp only [Pi.mul_def] at hNadd hTadd
  rw [hNr, hTt, hNadd, hTadd, radialPartial_mul df dNg, radialPartial_mul dg dNf,
    angularPartial_mul df dTg, angularPartial_mul dg dTf]
  simp only [symmetricNormalFlux, symmetricAngularFlux, n05PrincipalPair]
  ring

/-- At a common zero of the two test factors, only the principal form
survives. The multiplier contributes its value, not its derivatives. -/
theorem n05_divergenceOperator_height_product
    {L : SymmetricCoefficients} {h f g : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ L.a x) (hB : ContDiffAt ℝ ∞ L.b x)
    (hC : ContDiffAt ℝ ∞ L.c x)
    (hh : ContDiffAt ℝ ∞ h x)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hf0 : f x = 0) (hg0 : g x = 0) :
    divergenceOperator L (fun y => h y * (f y * g y)) x =
      2 * h x * n05PrincipalPair L f g x := by
  rw [n05_divergenceOperator_mul hA hB hC hh (hf.mul hg),
    n05_divergenceOperator_mul hA hB hC hf hg]
  simp only [n05PrincipalPair, radialPartial_mul
      (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)),
    angularPartial_mul
      (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)),
    hf0, hg0, zero_mul, mul_zero, zero_add, add_zero]
  ring

/-- Actual conjugation on smooth functions determines the principal form.
The zero-order potential drops out on the centered quadratic test f*g.
This is the form needed to test the N04 canonical-operator identity. -/
theorem n05_principalPair_of_conjugation
    {L A : SymmetricCoefficients} {Ψ : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint} {v : ℝ}
    (hLa : ContDiffAt ℝ ∞ L.a x) (hLb : ContDiffAt ℝ ∞ L.b x)
    (hLc : ContDiffAt ℝ ∞ L.c x)
    (hAa : ContDiffAt ℝ ∞ A.a (Ψ x)) (hAb : ContDiffAt ℝ ∞ A.b (Ψ x))
    (hAc : ContDiffAt ℝ ∞ A.c (Ψ x))
    (hh : ContDiffAt ℝ ∞ h x) (hΨ : ContDiffAt ℝ ∞ Ψ x)
    (hJ : planeJacobian Ψ x ≠ 0)
    (hoperator : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x / |planeJacobian Ψ x| *
          divergenceOperator L (fun y => h y * W (Ψ y)) x =
        divergenceOperator A W (Ψ x) + v * W (Ψ x))
    {f g : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hf0 : f (Ψ x) = 0) (hg0 : g (Ψ x) = 0) :
    h x ^ 2 * n05PrincipalPair L (fun y => f (Ψ y)) (fun y => g (Ψ y)) x =
      |planeJacobian Ψ x| * n05PrincipalPair A f g (Ψ x) := by
  have hfg := hoperator (fun y => f y * g y) (hf.mul hg)
  have htest := n05_divergenceOperator_height_product hLa hLb hLc hh
    (hf.contDiffAt.comp x hΨ) (hg.contDiffAt.comp x hΨ) hf0 hg0
  simp only [Function.comp_apply] at htest
  rw [htest, n05_divergenceOperator_mul hAa hAb hAc hf.contDiffAt hg.contDiffAt]
    at hfg
  simp only [hf0, hg0, zero_mul, mul_zero, zero_add, add_zero] at hfg
  have hJabs : |planeJacobian Ψ x| ≠ 0 := abs_ne_zero.mpr hJ
  field_simp [hJabs] at hfg
  simpa only [Function.comp_def] using hfg

/-- Algebraic determinant of a transported symmetric two-dimensional
principal form. This will be applied to actual coordinate partials. -/
theorem n05_principal_determinant_algebra
    (a b c xr xt yr yt : ℝ) :
    (a * xr ^ 2 + 2 * b * xr * xt + c * xt ^ 2) *
        (a * yr ^ 2 + 2 * b * yr * yt + c * yt ^ 2) -
      (a * xr * yr + b * (xr * yt + xt * yr) + c * xt * yt) ^ 2 =
        (a * c - b ^ 2) * (xr * yt - xt * yr) ^ 2 := by
  ring

/-- The coordinate determinant written using actual scalar partials is
the actual Frechet Jacobian already used by N04. -/
theorem n05_planeJacobian_eq_partials
    {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hΨ : DifferentiableAt ℝ Ψ x) :
    planeJacobian Ψ x =
      radialPartial (fun y => (Ψ y).1) x * angularPartial (fun y => (Ψ y).2) x -
        angularPartial (fun y => (Ψ y).1) x * radialPartial (fun y => (Ψ y).2) x := by
  have hfst := hΨ.hasFDerivAt.fst
  have hsnd := hΨ.hasFDerivAt.snd
  unfold planeJacobian radialPartial angularPartial
  rw [hfst.fderiv, hsnd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  ring

end ContinuousFlexibility.Statements
