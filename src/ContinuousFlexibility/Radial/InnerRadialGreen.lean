import ContinuousFlexibility.Radial.InnerPositiveGap

/-!
# Green identities at the actual radial cuts

The signs here are the outward signs at the left and right endpoints.
For a zero-boundary forced solution and a homogeneous Poisson function,
the total outward flux pairing is minus their physical source pairing.
This is the local identity behind `flux D = -T*` in the inner assembly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff

def innerRadialGapMixedBoundary (w u v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (v b * (w b * deriv u b) - u b * (w b * deriv v b)) -
    (v a * (w a * deriv u a) - u a * (w a * deriv v a))

theorem innerRadialJacobi_continuousOn {a b j : ℝ} (ha : 0 < a)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) :
    ContinuousOn (radialJacobi (j ^ 2) w u) (Icc a b) := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hflux := (contDiff_infty_iff_deriv.mp (hw.mul hdu)).2.continuous
  have hdw := (contDiff_infty_iff_deriv.mp hw).2.continuous
  exact hflux.continuousOn.sub
    (((continuous_const.mul hdw).continuousOn.div continuous_id.continuousOn
      (fun r h => (ha.trans_le h.1).ne')).mul hu.continuous.continuousOn)

/-- The Lagrange identity for the actual radial differential expression. -/
theorem innerRadialGap_lagrange {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w u v : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    (∫ r in a..b, v r * radialJacobi (j ^ 2) w u r -
      u r * radialJacobi (j ^ 2) w v r) = innerRadialGapMixedBoundary w u v a b := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hdv := (contDiff_infty_iff_deriv.mp hv).2
  have hfluxu := hw.mul hdu
  have hfluxv := hw.mul hdv
  have hc := (hv.continuous.continuousOn.mul
    (innerRadialJacobi_continuousOn (b := b) (j := j) ha hw hu)).sub
      (hu.continuous.continuousOn.mul (innerRadialJacobi_continuousOn (b := b) (j := j) ha hw hv))
  unfold innerRadialGapMixedBoundary
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => v r * (w r * deriv u r) - u r * (w r * deriv v r)) _
    (hc.intervalIntegrable_of_Icc hab)
  intro r _
  convert (((hv.differentiable (by simp) r).hasDerivAt.mul
      (hfluxu.differentiable (by simp) r).hasDerivAt).sub
    ((hu.differentiable (by simp) r).hasDerivAt.mul
      (hfluxv.differentiable (by simp) r).hasDerivAt)) using 1
  unfold radialJacobi
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring

/-- The source is measured with `dμ = (12 w / r²) dr`. At zero Dirichlet
values the two outward fluxes pair with the Poisson boundary data with
the negative adjoint sign. -/
theorem innerRadialGap_forced_flux {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w u v F : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hua : u a = 0) (hub : u b = 0)
    (huEq : ∀ r ∈ Icc a b,
      radialJacobi (j ^ 2) w u r = -(12 * w r / r ^ 2) * F r)
    (hvEq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w v r = 0) :
    v b * (w b * deriv u b) - v a * (w a * deriv u a) =
      -(∫ r in a..b, (12 * w r / r ^ 2) * F r * v r) := by
  have h := innerRadialGap_lagrange (j := j) hab ha hw hu hv
  have hi : (∫ r in a..b, v r * radialJacobi (j ^ 2) w u r -
      u r * radialJacobi (j ^ 2) w v r) =
        -(∫ r in a..b, (12 * w r / r ^ 2) * F r * v r) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
    dsimp only
    rw [huEq r hr', hvEq r hr']
    ring
  rw [hi] at h
  simpa only [innerRadialGapMixedBoundary, hua, hub, zero_mul, sub_zero] using h.symm

end ContinuousFlexibility.Radial
