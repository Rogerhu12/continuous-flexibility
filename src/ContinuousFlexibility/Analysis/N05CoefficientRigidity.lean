import ContinuousFlexibility.Analysis.N05PolynomialProbes
import ContinuousFlexibility.Radial.RadialHeight

/-!
# Coefficient regularity forced by actual polynomial tests

The Frechet derivative is totalized as zero for a nondifferentiable function.
That convention cannot be used to hide an irregular coefficient: the probe
identities below force the relevant fluxes to be differentiable.  No regularity
of the mixed or angular coefficient is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Two radial probes force differentiability of the mixed coefficient.
If it were irregular, the normal flux derivatives would both vanish, while
the angular fluxes have the same angular slice and cannot have the two
distinct nonzero derivatives demanded by the operator identity. -/
theorem n05_mixed_differentiable_of_radialProbes
    {L : SymmetricCoefficients} {x : PolarPoint}
    (ha : DifferentiableAt ℝ L.a x) (ha0 : L.a x ≠ 0)
    (hprobe : ∀ s : ℝ, divergenceOperator L (n05RadialProbe x s) x = 2 * s * L.a x) :
    DifferentiableAt ℝ L.b x := by
  by_contra hb
  have hr := (n05RadialLinear_contDiff x).differentiable (by simp) x
  have hNnot (s : ℝ) : ¬ DifferentiableAt ℝ
      (fun y => 2 * s * L.a y * n05RadialLinear x y + L.b y) x := by
    intro hN
    have hs : DifferentiableAt ℝ
        (fun y => 2 * s * L.a y * n05RadialLinear x y) x :=
      ((differentiableAt_const (2 * s)).mul ha).mul hr
    apply hb
    convert hN.sub hs using 1
    funext y
    ring
  have hslice (s : ℝ) (hs : s ≠ 0) :
      HasDerivAt (fun θ => L.c (x.1, θ)) (2 * s * L.a x) x.2 := by
    have hop := hprobe s
    rw [n05_divergence_radialProbe_flux] at hop
    have hNr : radialPartial
        (fun y => 2 * s * L.a y * n05RadialLinear x y + L.b y) x = 0 := by
      simp only [radialPartial, fderiv_zero_of_not_differentiableAt (hNnot s),
        ContinuousLinearMap.zero_apply]
    rw [hNr, zero_add] at hop
    have hnonzero : 2 * s * L.a x ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hs) ha0
    have hT : DifferentiableAt ℝ
        (fun y => 2 * s * L.b y * n05RadialLinear x y + L.c y) x := by
      by_contra hbad
      have hzero : angularPartial
          (fun y => 2 * s * L.b y * n05RadialLinear x y + L.c y) x = 0 := by
        simp only [angularPartial, fderiv_zero_of_not_differentiableAt hbad,
          ContinuousLinearMap.zero_apply]
      rw [hzero] at hop
      exact hnonzero hop.symm
    have hslice' := Radial.hasDerivAt_angularSlice hT
    rw [hop] at hslice'
    simpa only [n05RadialLinear, sub_self, mul_zero, zero_add] using hslice'
  have heq := (hslice 1 (by norm_num)).unique (hslice 2 (by norm_num))
  apply ha0
  linarith only [heq]

/-- An angular probe with nonzero radial-reference type forces the angular
coefficient to be differentiable; multiplying by its nonvanishing angular
factor cannot remove a failure of differentiability. -/
theorem n05_angular_differentiable_of_angularProbes
    {L : SymmetricCoefficients} {x : PolarPoint} {c : ℝ}
    (hb : DifferentiableAt ℝ L.b x) (hc : c ≠ 0)
    (hprobe : ∀ s : ℝ, divergenceOperator L (n05AngularProbe x s) x = 2 * s * c) :
    DifferentiableAt ℝ L.c x := by
  by_contra hbad
  have ht := (n05AngularLinear_contDiff x).differentiable (by simp) x
  have hvalue (s : ℝ) : radialPartial L.b x = 2 * s * c := by
    have hscaled : DifferentiableAt ℝ (fun y => 2 * s * n05AngularLinear x y) x :=
      (differentiableAt_const (2 * s)).mul ht
    have hfactor : ContDiff ℝ ∞ (fun y => 1 + 2 * s * n05AngularLinear x y) :=
      contDiff_const.add (contDiff_const.mul (n05AngularLinear_contDiff x))
    have hfactor' := hfactor.differentiable (by simp) x
    have hfactor0 : 1 + 2 * s * n05AngularLinear x x ≠ 0 := by simp
    have hTnot : ¬ DifferentiableAt ℝ
        (fun y => L.c y * (1 + 2 * s * n05AngularLinear x y)) x := by
      intro hT
      have hnear : ∀ᶠ y in 𝓝 x, 1 + 2 * s * n05AngularLinear x y ≠ 0 :=
        (isOpen_ne_fun hfactor.continuous continuous_const).mem_nhds hfactor0
      apply hbad
      apply (hT.div hfactor' hfactor0).congr_of_eventuallyEq
      filter_upwards [hnear] with y hy
      change L.c y = L.c y * (1 + 2 * s * n05AngularLinear x y) /
        (1 + 2 * s * n05AngularLinear x y)
      exact (mul_div_cancel_right₀ _ hy).symm
    have hNr : radialPartial
        (fun y => L.b y * (1 + 2 * s * n05AngularLinear x y)) x =
          radialPartial L.b x := by
      rw [radialPartial_mul hb hfactor',
        radialPartial_add differentiableAt_const hscaled,
        radialPartial_mul (differentiableAt_const (2 * s)) ht]
      simp only [n05AngularLinear_self, n05AngularLinear_radial, radialPartial_const,
        mul_zero, zero_mul, add_zero, zero_add, mul_one]
    have hTzero : angularPartial
        (fun y => L.c y * (1 + 2 * s * n05AngularLinear x y)) x = 0 := by
      simp only [angularPartial, fderiv_zero_of_not_differentiableAt hTnot,
        ContinuousLinearMap.zero_apply]
    have hop := hprobe s
    rw [n05_divergence_angularProbe_flux, hNr, hTzero, add_zero] at hop
    exact hop
  have h0 := hvalue 0
  have h1 := hvalue 1
  apply hc
  linarith only [h0, h1]

/-- Actual radial, angular, and mixed quadratic probes identify both
unknown coefficients and establish the differentiability needed to use
the product rule afterwards. -/
theorem n05_coefficients_rigid_at
    {L : SymmetricCoefficients} {x : PolarPoint} {c : ℝ}
    (ha : DifferentiableAt ℝ L.a x) (ha0 : L.a x ≠ 0) (hc0 : c ≠ 0)
    (hR : ∀ s : ℝ, divergenceOperator L (n05RadialProbe x s) x = 2 * s * L.a x)
    (hT : ∀ s : ℝ, divergenceOperator L (n05AngularProbe x s) x = 2 * s * c)
    (hRT : divergenceOperator L (n05MixedProbe x) x = 0) :
    DifferentiableAt ℝ L.b x ∧ DifferentiableAt ℝ L.c x ∧ L.b x = 0 ∧ L.c x = c := by
  have hb := n05_mixed_differentiable_of_radialProbes ha ha0 hR
  have hc := n05_angular_differentiable_of_angularProbes hb hc0 hT
  have hB := hRT
  rw [n05_divergence_mixedProbe ha hb hc] at hB
  have h0 := hT 0
  have h1 := hT 1
  rw [n05_divergence_angularProbe hb hc] at h0 h1
  exact ⟨hb, hc, by linarith only [hB], by linarith only [h0, h1]⟩

end ContinuousFlexibility.Statements

