module

public import ContinuousFlexibility.Analysis.N06EllipticProbeRegularity
public import ContinuousFlexibility.Analysis.N05ReferenceQuadraticTests

/-!
# Genuine conjugation supplies the elliptic probe responses

Only the physical coefficients and the forward chart are assumed smooth.
The canonical coefficients are initially arbitrary functions. Centered
polynomials in the actual operator identity force their differentiability.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n06_eventually_differentiableAt
    {f : PolarPoint → ℝ} {x : PolarPoint} (hf : ContDiffAt ℝ ∞ f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
  have h1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  filter_upwards [h1.eventually (by norm_num)] with y hy
  exact hy.differentiableAt one_ne_zero

/-- Local smoothness suffices for linearity of the actual physical operator. -/
theorem n06_divergenceOperator_add_smul
    {L : SymmetricCoefficients} {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ L.a x) (hB : ContDiffAt ℝ ∞ L.b x)
    (hC : ContDiffAt ℝ ∞ L.c x)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (s : ℝ) :
    divergenceOperator L (fun y => f y + s * g y) x =
      divergenceOperator L f x + s * divergenceOperator L g x := by
  have hN : symmetricNormalFlux L.a L.b (fun y => f y + s * g y) =ᶠ[𝓝 x]
      (fun y => symmetricNormalFlux L.a L.b f y + s * symmetricNormalFlux L.a L.b g y) := by
    filter_upwards [n06_eventually_differentiableAt hf,
      n06_eventually_differentiableAt hg] with y hfy hgy
    simp only [symmetricNormalFlux, radialPartial_add hfy (hgy.const_mul s),
      angularPartial_add hfy (hgy.const_mul s),
      radialPartial_mul (differentiableAt_const s) hgy,
      angularPartial_mul (differentiableAt_const s) hgy,
      radialPartial_const, angularPartial_const]
    ring
  have hT : symmetricAngularFlux L.b L.c (fun y => f y + s * g y) =ᶠ[𝓝 x]
      (fun y => symmetricAngularFlux L.b L.c f y + s * symmetricAngularFlux L.b L.c g y) := by
    filter_upwards [n06_eventually_differentiableAt hf,
      n06_eventually_differentiableAt hg] with y hfy hgy
    simp only [symmetricAngularFlux, radialPartial_add hfy (hgy.const_mul s),
      angularPartial_add hfy (hgy.const_mul s),
      radialPartial_mul (differentiableAt_const s) hgy,
      angularPartial_mul (differentiableAt_const s) hgy,
      radialPartial_const, angularPartial_const]
    ring
  have hNf := (contDiffAt_symmetricNormalFlux hA hB hf).differentiableAt (by simp)
  have hNg := (contDiffAt_symmetricNormalFlux hA hB hg).differentiableAt (by simp)
  have hTf := (contDiffAt_symmetricAngularFlux hB hC hf).differentiableAt (by simp)
  have hTg := (contDiffAt_symmetricAngularFlux hB hC hg).differentiableAt (by simp)
  have hNr := congrArg (fun F : PolarPoint →L[ℝ] ℝ => F (1, 0))
    (hN.fderiv_eq (𝕜 := ℝ))
  have hTt := congrArg (fun F : PolarPoint →L[ℝ] ℝ => F (0, 1))
    (hT.fderiv_eq (𝕜 := ℝ))
  change radialPartial (symmetricNormalFlux L.a L.b (fun y => f y + s * g y)) x =
    radialPartial (fun y => symmetricNormalFlux L.a L.b f y + s * symmetricNormalFlux L.a L.b g y) x at hNr
  change angularPartial (symmetricAngularFlux L.b L.c (fun y => f y + s * g y)) x =
    angularPartial (fun y => symmetricAngularFlux L.b L.c f y + s * symmetricAngularFlux L.b L.c g y) x at hTt
  change symmetricDivergence L.a L.b L.c (fun y => f y + s * g y) x =
    symmetricDivergence L.a L.b L.c f x + s * symmetricDivergence L.a L.b L.c g x
  unfold symmetricDivergence
  rw [hNr, hTt, radialPartial_add hNf (hNg.const_mul s),
    angularPartial_add hTf (hTg.const_mul s),
    radialPartial_mul (differentiableAt_const s) hNg,
    angularPartial_mul (differentiableAt_const s) hTg]
  simp only [radialPartial_const, angularPartial_const]
  ring

/-- A centered polynomial has an affine principal response, as computed
from the true physical divergence and forward chart. -/
theorem n06_conjugation_polynomial_response
    {L A : SymmetricCoefficients} {Ψ : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint} {v : ℝ}
    (hLa : ContDiffAt ℝ ∞ L.a x) (hLb : ContDiffAt ℝ ∞ L.b x)
    (hLc : ContDiffAt ℝ ∞ L.c x)
    (hh : ContDiffAt ℝ ∞ h x) (hΨ : ContDiffAt ℝ ∞ Ψ x)
    (hoperator : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x / |planeJacobian Ψ x| *
          divergenceOperator L (fun y => h y * W (Ψ y)) x =
        divergenceOperator A W (Ψ x) + v * W (Ψ x))
    {f g : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hf0 : f (Ψ x) = 0) (hg0 : g (Ψ x) = 0) (s : ℝ) :
    divergenceOperator A (fun y => f y + s * g y ^ 2) (Ψ x) =
      h x / |planeJacobian Ψ x| * divergenceOperator L (fun y => h y * f (Ψ y)) x +
        2 * s * (h x ^ 2 / |planeJacobian Ψ x| *
          n05PrincipalPair L (fun y => g (Ψ y)) (fun y => g (Ψ y)) x) := by
  have hfg := hoperator (fun y => f y + s * g y ^ 2)
    (hf.add (contDiff_const.mul (hg.pow 2)))
  simp only [hf0, hg0, zero_pow (by omega : (2 : ℕ) ≠ 0),
    mul_zero, zero_add, add_zero] at hfg
  have he : (fun y => h y * (f (Ψ y) + s * g (Ψ y) ^ 2)) =
      (fun y => h y * f (Ψ y) + s * (h y * (g (Ψ y) * g (Ψ y)))) := by
    funext y
    ring
  have hadd := n06_divergenceOperator_add_smul hLa hLb hLc
    (hh.mul (hf.contDiffAt.comp x hΨ))
    (hh.mul ((hg.contDiffAt.comp x hΨ).mul (hg.contDiffAt.comp x hΨ))) s
  have hquad := n05_divergenceOperator_height_product hLa hLb hLc hh
    (hg.contDiffAt.comp x hΨ) (hg.contDiffAt.comp x hΨ) hg0 hg0
  simp only [Function.comp_def] at hadd hquad
  rw [he, hadd, hquad] at hfg
  rw [← hfg]
  simp only [div_eq_mul_inv]
  ring

/-- The actual elliptic principal responses force all three canonical
coefficient fields to be differentiable at the image point. -/
theorem n06_coefficients_differentiable_of_conjugation
    {L A : SymmetricCoefficients} {Ψ : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint} {v : ℝ}
    (hLa : ContDiffAt ℝ ∞ L.a x) (hLb : ContDiffAt ℝ ∞ L.b x)
    (hLc : ContDiffAt ℝ ∞ L.c x)
    (hh : ContDiffAt ℝ ∞ h x) (hΨ : ContDiffAt ℝ ∞ Ψ x)
    (hh0 : h x ≠ 0) (hJ : planeJacobian Ψ x ≠ 0)
    (hrr : n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).1) x ≠ 0)
    (htt : n05PrincipalPair L (fun y => (Ψ y).2) (fun y => (Ψ y).2) x ≠ 0)
    (hoperator : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x / |planeJacobian Ψ x| *
          divergenceOperator L (fun y => h y * W (Ψ y)) x =
        divergenceOperator A W (Ψ x) + v * W (Ψ x)) :
    DifferentiableAt ℝ A.a (Ψ x) ∧ DifferentiableAt ℝ A.b (Ψ x) ∧
      DifferentiableAt ℝ A.c (Ψ x) := by
  let α := h x ^ 2 / |planeJacobian Ψ x| *
    n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).1) x
  let γ := h x ^ 2 / |planeJacobian Ψ x| *
    n05PrincipalPair L (fun y => (Ψ y).2) (fun y => (Ψ y).2) x
  have hα : α ≠ 0 := mul_ne_zero (div_ne_zero (pow_ne_zero _ hh0) (abs_ne_zero.mpr hJ)) hrr
  have hγ : γ ≠ 0 := mul_ne_zero (div_ne_zero (pow_ne_zero _ hh0) (abs_ne_zero.mpr hJ)) htt
  have hR (s : ℝ) := n06_conjugation_polynomial_response hLa hLb hLc hh hΨ hoperator
    (n05RadialLinear_contDiff (Ψ x)) (n05RadialLinear_contDiff (Ψ x))
    (n05RadialLinear_self _) (n05RadialLinear_self _) s
  have hT (s : ℝ) := n06_conjugation_polynomial_response hLa hLb hLc hh hΨ hoperator
    (n05AngularLinear_contDiff (Ψ x)) (n05AngularLinear_contDiff (Ψ x))
    (n05AngularLinear_self _) (n05AngularLinear_self _) s
  have hPr : n05PrincipalPair L (fun y => n05RadialLinear (Ψ x) (Ψ y))
      (fun y => n05RadialLinear (Ψ x) (Ψ y)) x =
      n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).1) x :=
    n05PrincipalPair_sub_const (hΨ.fst.differentiableAt (by simp))
      (hΨ.fst.differentiableAt (by simp)) _ _
  have hPt : n05PrincipalPair L (fun y => n05AngularLinear (Ψ x) (Ψ y))
      (fun y => n05AngularLinear (Ψ x) (Ψ y)) x =
      n05PrincipalPair L (fun y => (Ψ y).2) (fun y => (Ψ y).2) x :=
    n05PrincipalPair_sub_const (hΨ.snd.differentiableAt (by simp))
      (hΨ.snd.differentiableAt (by simp)) _ _
  obtain ⟨ha, hc⟩ := n06_diagonal_differentiable_of_pure_probes (L := A) (x := Ψ x)
    (dr := h x / |planeJacobian Ψ x| *
      divergenceOperator L (fun y => h y * n05RadialLinear (Ψ x) (Ψ y)) x)
    (dt := h x / |planeJacobian Ψ x| *
      divergenceOperator L (fun y => h y * n05AngularLinear (Ψ x) (Ψ y)) x) hα hγ
    (fun s => by
      have ht := hR s
      rw [hPr] at ht
      have heq : n06PureQuadraticProbe (ContinuousLinearMap.fst ℝ ℝ ℝ) (Ψ x) s =
          (fun y => n05RadialLinear (Ψ x) y + s * n05RadialLinear (Ψ x) y ^ 2) := rfl
      rw [heq]
      exact ht)
    (fun s => by
      have ht := hT s
      rw [hPt] at ht
      have heq : n06PureQuadraticProbe (ContinuousLinearMap.snd ℝ ℝ ℝ) (Ψ x) s =
          (fun y => n05AngularLinear (Ψ x) y + s * n05AngularLinear (Ψ x) y ^ 2) := rfl
      rw [heq]
      exact ht)
  refine ⟨ha, ?_, hc⟩
  apply n06_mixed_differentiable_of_biased_probes (d := h x / |planeJacobian Ψ x| *
    divergenceOperator L (fun y => h y *
      (n05RadialLinear (Ψ x) (Ψ y) + n05AngularLinear (Ψ x) (Ψ y))) x) ha hc hα
  intro s
  have h := n06_conjugation_polynomial_response hLa hLb hLc hh hΨ hoperator
    ((n05RadialLinear_contDiff (Ψ x)).add (n05AngularLinear_contDiff (Ψ x)))
    (n05RadialLinear_contDiff (Ψ x))
    (by simp only [n05RadialLinear_self, n05AngularLinear_self, zero_add])
    (n05RadialLinear_self _) s
  rw [hPr] at h
  convert h using 1
  apply congrArg (fun W => divergenceOperator A W (Ψ x))
  funext y
  simp only [n06PureQuadraticProbe, ContinuousLinearMap.coe_fst', n05RadialLinear,
    n05AngularLinear]
  ring

end ContinuousFlexibility.Statements
