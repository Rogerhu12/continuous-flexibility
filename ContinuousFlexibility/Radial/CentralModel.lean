import ContinuousFlexibility.Radial.CentralRadiusMetric

/-!
# The actual central profile and its surviving mode

The smooth radial profile defined using the proved inverse radius has
the required turning coefficient. Its explicit positive mode solves the
actual radial Jacobi equation. This is a differential kernel statement;
the closed spectral domain and its full kernel classification are separate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem centralRadialProfile_deriv_scaled (c x : ℝ) :
    deriv (centralRadialProfile c) (centralRadius x) * deriv centralRadius x =
      c * centralDensityRoot x ^ 2 * centralRadius x * (x ^ 2 - centralOscillatorA) := by
  have hR := (contDiff_centralRadius.differentiable (by simp) x).hasDerivAt
  have hRdiff : ContDiff ℝ ∞ (deriv centralRadius) :=
    (contDiff_infty_iff_deriv.mp contDiff_centralRadius).2
  have hR' := (hRdiff.differentiable (by simp) x).hasDerivAt
  have hs := hasDerivAt_centralDensityRoot x
  have hM : HasDerivAt (centralPulledProfile c)
      (c * (2 * centralDensityRoot x * deriv centralDensityRoot x * deriv centralRadius x +
        centralDensityRoot x ^ 2 * deriv (deriv centralRadius) x)) x := by
    convert ((hs.pow 2).mul hR').const_mul c using 1
    · funext y
      simp only [centralPulledProfile, Pi.mul_apply, Pi.pow_apply]
      ring
    · rw [deriv_centralDensityRoot]
      simp only [Pi.pow_apply]
      ring
  have hcomp := ((contDiffAt_centralRadialProfile c x).differentiableAt (by simp)).hasDerivAt.comp x hR
  have hd := hcomp.unique (hM.congr_of_eventuallyEq
    (Eventually.of_forall (centralRadialProfile_pullback c)))
  have hdd : deriv (deriv centralRadius) x = 2 * centralRadiusA * deriv centralRadius x +
      (x ^ 2 - centralOscillatorA) * centralRadius x := by
    nlinarith [centralRadius_ode x]
  rw [hd, hdd, deriv_centralDensityRoot]
  ring

theorem centralRadialProfile_deriv_zero_iff {c : ℝ} (hc : 0 < c) (x : ℝ) :
    deriv (centralRadialProfile c) (centralRadius x) = 0 ↔ x ^ 2 = centralOscillatorA := by
  have hcoef : c * centralDensityRoot x ^ 2 * centralRadius x ≠ 0 :=
    (mul_pos (mul_pos hc (sq_pos_of_pos (centralDensityRoot_pos x))) (centralRadius_pos x)).ne'
  have hD := centralRadialProfile_deriv_scaled c x
  constructor
  · intro hz
    rw [hz, zero_mul] at hD
    exact sub_eq_zero.mp ((mul_eq_zero.mp hD.symm).resolve_left hcoef)
  · intro hz
    rw [hz, sub_self, mul_zero] at hD
    exact (mul_eq_zero.mp hD).resolve_right (deriv_centralRadius_pos x).ne'

theorem centralRadialProfile_deriv_pos_iff {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 < deriv (centralRadialProfile c) (centralRadius x) ↔ centralOscillatorA < x ^ 2 := by
  rw [← mul_pos_iff_of_pos_right (deriv_centralRadius_pos x), centralRadialProfile_deriv_scaled,
    mul_pos_iff_of_pos_left
      (mul_pos (mul_pos hc (sq_pos_of_pos (centralDensityRoot_pos x))) (centralRadius_pos x)),
    sub_pos]

theorem centralRadialProfile_deriv_neg_iff {c : ℝ} (hc : 0 < c) (x : ℝ) :
    deriv (centralRadialProfile c) (centralRadius x) < 0 ↔ x ^ 2 < centralOscillatorA := by
  have hcoef := mul_pos (mul_pos hc (sq_pos_of_pos (centralDensityRoot_pos x))) (centralRadius_pos x)
  have hprod : deriv (centralRadialProfile c) (centralRadius x) * deriv centralRadius x < 0 ↔
      x ^ 2 < centralOscillatorA := by
    rw [centralRadialProfile_deriv_scaled]
    have hh := mul_lt_mul_iff_right₀ hcoef (b := x ^ 2 - centralOscillatorA) (c := (0 : ℝ))
    simpa only [mul_zero, sub_neg] using hh
  rw [← hprod]
  have hh := mul_lt_mul_iff_left₀ (deriv_centralRadius_pos x)
    (b := deriv (centralRadialProfile c) (centralRadius x)) (c := (0 : ℝ))
  simpa only [zero_mul] using hh.symm

def centralOscillatorGround (x : ℝ) : ℝ := exp (-x ^ 2)

def centralKernelHeight (r : ℝ) : ℝ :=
  exp (centralRadiusA * centralModelCoordinate r - centralModelCoordinate r ^ 2)

theorem contDiff_centralOscillatorGround : ContDiff ℝ ∞ centralOscillatorGround :=
  (contDiff_id.pow 2).neg.exp

theorem hasDerivAt_centralOscillatorGround (x : ℝ) :
    HasDerivAt centralOscillatorGround (-2 * x * centralOscillatorGround x) x := by
  convert ((hasDerivAt_id x).pow 2).neg.exp using 1
  · funext y
    simp only [centralOscillatorGround, Pi.pow_apply, Pi.neg_apply, id_eq]
  · simp only [centralOscillatorGround, Pi.pow_apply, Pi.neg_apply, id_eq]
    ring

theorem deriv_centralOscillatorGround (x : ℝ) :
    deriv centralOscillatorGround x = -2 * x * centralOscillatorGround x :=
  (hasDerivAt_centralOscillatorGround x).deriv

theorem deriv_deriv_centralOscillatorGround (x : ℝ) :
    deriv (deriv centralOscillatorGround) x = (4 * x ^ 2 - 2) * centralOscillatorGround x := by
  have hd : deriv centralOscillatorGround = fun y => -2 * y * centralOscillatorGround y :=
    funext deriv_centralOscillatorGround
  rw [hd]
  convert (((hasDerivAt_id x).const_mul (-2)).mul (hasDerivAt_centralOscillatorGround x)).deriv using 1
  · rfl
  · simp only [id_eq]
    ring

theorem centralOscillatorGround_liouville (x : ℝ) :
    liouvilleSchrodinger 4 centralRadius centralDensityRoot centralOscillatorGround x = 0 := by
  unfold liouvilleSchrodinger
  rw [centralRadius_liouvilleRho, centralDensityRoot_liouvilleV0, deriv_deriv_centralOscillatorGround]
  ring_nf
  rw [centralRadiusA_sq]
  ring

theorem centralKernelHeight_pos (r : ℝ) : 0 < centralKernelHeight r := exp_pos _

theorem centralKernelHeight_pullback (x : ℝ) :
    centralKernelHeight (centralRadius x) = exp (centralRadiusA * x - x ^ 2) := by
  simp only [centralKernelHeight, centralModelCoordinate_radius]

theorem centralKernelHeight_liouville_pullback (x : ℝ) :
    centralKernelHeight (centralRadius x) = centralOscillatorGround x / centralDensityRoot x := by
  rw [centralKernelHeight_pullback]
  unfold centralOscillatorGround centralDensityRoot
  rw [← exp_sub]
  congr 1
  ring

theorem contDiffAt_centralKernelHeight (x : ℝ) :
    ContDiffAt ℝ ∞ centralKernelHeight (centralRadius x) := by
  have ht := contDiffAt_centralModelCoordinate x
  exact ((contDiffAt_const.mul ht).sub (ht.pow 2)).exp

/-- A genuine positive solution of `L₂ u = 0` for the genuine positive
central radial profile. No height equation or spectral kernel is a premise. -/
theorem radialJacobi_centralKernel (c x : ℝ) :
    radialJacobi 4 (centralRadialProfile c) centralKernelHeight (centralRadius x) = 0 := by
  have hR := contDiff_centralRadius.differentiable (by simp)
  have hs := contDiff_centralDensityRoot.differentiable (by simp)
  have hψ := contDiff_centralOscillatorGround.differentiable (by simp)
  have hR₂ := (contDiff_infty_iff_deriv.mp contDiff_centralRadius).2.differentiable (by simp) x
  have hs₂ := (contDiff_infty_iff_deriv.mp contDiff_centralDensityRoot).2.differentiable (by simp) x
  have hψ₂ := (contDiff_infty_iff_deriv.mp contDiff_centralOscillatorGround).2.differentiable (by simp) x
  have hw := contDiffAt_centralRadialProfile c x
  have hu := contDiffAt_centralKernelHeight x
  have hflux : DifferentiableAt ℝ (fun r => centralRadialProfile c r * deriv centralKernelHeight r)
      (centralRadius x) :=
    (hw.mul (hu.derivWithin (m := ∞) (by simp))).differentiableAt (by simp)
  have hL := radialJacobi_liouville (a := 4) (c := c)
    (Eventually.of_forall hR) (Eventually.of_forall hs) (Eventually.of_forall hψ)
    (Eventually.of_forall (fun t => (contDiffAt_centralKernelHeight t).differentiableAt (by simp)))
    hR₂ hs₂ hψ₂ (hw.differentiableAt (by simp)) hflux
    (centralRadius_pos x).ne' (deriv_centralRadius_pos x).ne' (centralDensityRoot_pos x).ne'
    (Eventually.of_forall (centralRadialProfile_pullback c))
    (Eventually.of_forall centralKernelHeight_liouville_pullback)
  rw [centralOscillatorGround_liouville, mul_zero] at hL
  exact hL

end ContinuousFlexibility.Radial
