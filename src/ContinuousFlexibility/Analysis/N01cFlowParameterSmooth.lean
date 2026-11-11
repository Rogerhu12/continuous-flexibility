import ContinuousFlexibility.Analysis.N01cFlowParameterContinuity
import ContinuousFlexibility.Analysis.OneHighCircleFlowTimeChange

/-!
# Genuine smooth dependence of a classical trajectory on a scalar parameter

The parameter derivative is obtained from exact differences of solutions
with different speeds.  Its integrating-factor expression is then used
to bootstrap actual joint differentiability of every finite order.  No
parameter derivative or directional tower of the trajectory is a premise.

A flat smooth time change reduces a supplied compact-interval family to
the global bootstrap.  Consequently every time slice, including both
endpoint slices, is smooth in the actual speed parameter.  The speed is
assumed jointly smooth in its scalar parameter, time and angle; applying
this result to the annular family still requires the genuine smooth
regularized speed on its state neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Variation of constants with either orientation of the endpoints.
The fundamental theorem is applied to the actual integrating factor. -/
theorem scalar_inhomogeneousODE_eq_exp_mul_global
    {κ F y : ℝ → ℝ} (hκ : Continuous κ) (hF : Continuous F)
    (hdy : ∀ t : ℝ, HasDerivAt y (κ t * y t + F t) t) (a b : ℝ) :
    y b = Real.exp (∫ r in a..b, κ r) *
      (y a + ∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) * F t) := by
  have hprimitive (t : ℝ) :
      HasDerivAt (fun x => ∫ r in a..x, κ r) (κ t) t :=
    (hκ.integral_hasStrictDerivAt a t).hasDerivAt
  have hprimitive_cont : Continuous (fun x => ∫ r in a..x, κ r) :=
    continuous_iff_continuousAt.mpr (fun t => (hprimitive t).continuousAt)
  have hforcing_cont : Continuous
      (fun t => Real.exp (-∫ r in a..t, κ r) * F t) :=
    (Real.continuous_exp.comp hprimitive_cont.neg).mul hF
  have hfactor_deriv (t : ℝ) :
      HasDerivAt (fun t => y t * Real.exp (-∫ r in a..t, κ r))
        (Real.exp (-∫ r in a..t, κ r) * F t) t := by
    have hd := (hdy t).mul (hprimitive t).neg.exp
    apply hd.congr_deriv
    simp only [Pi.neg_apply]
    ring
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hfactor_deriv t) (hforcing_cont.intervalIntegrable a b)
  have he : y b * Real.exp (-∫ r in a..b, κ r) =
      y a + ∫ t in a..b, Real.exp (-∫ r in a..t, κ r) * F t := by
    simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one] at hfund
    linarith
  calc
    y b = (y b * Real.exp (-∫ r in a..b, κ r)) *
        Real.exp (∫ r in a..b, κ r) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = (y a + ∫ t in a..b, Real.exp (-∫ r in a..t, κ r) * F t) *
        Real.exp (∫ r in a..b, κ r) := by rw [he]
    _ = _ := mul_comm _ _

/-- The actual angle derivative of a speed depending on one scalar parameter. -/
def circleSpeedAngleDeriv (G : ℝ × PolarPoint → ℝ) (p : ℝ × PolarPoint) : ℝ :=
  fderiv ℝ G p (0, (0, 1))

theorem contDiff_circleSpeedAngleDeriv {G : ℝ × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (circleSpeedAngleDeriv G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem circleSpeedAngleDeriv_eq_angularPartial {G : ℝ × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (q : ℝ) (p : PolarPoint) :
    circleSpeedAngleDeriv G (q, p) = angularPartial (fun x => G (q, x)) p := by
  have hs : HasFDerivAt (fun x : PolarPoint => G (q, x))
      ((fderiv ℝ G (q, p)).comp (ContinuousLinearMap.inr ℝ ℝ PolarPoint)) p :=
    (hG.differentiable (by simp) (q, p)).hasFDerivAt.comp p
      (hasFDerivAt_prodMk_right q p)
  change fderiv ℝ G (q, p) (0, (0, 1)) =
    fderiv ℝ (fun x : PolarPoint => G (q, x)) p (0, 1)
  rw [hs.fderiv]
  rfl

/-- The genuine first-variation expression, constructed from the actual
speed derivatives and the actual trajectory values. -/
def circleParameterTrajectoryDerivative (G : ℝ × PolarPoint → ℝ)
    (Θ : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  Real.exp (∫ r in (0 : ℝ)..p.2, circleSpeedAngleDeriv G (p.1, (r, Θ (p.1, r)))) *
    ∫ t in (0 : ℝ)..p.2,
      Real.exp (-(∫ r in (0 : ℝ)..t,
        circleSpeedAngleDeriv G (p.1, (r, Θ (p.1, r))))) *
          circleSpeedParameterDeriv G (p.1, (t, Θ (p.1, t)))

/-- Exact solution differences prove the first parameter derivative at
every real time, with no assumed parameter differentiability. -/
theorem globalCircleParameterTrajectory_hasDerivAt_parameter
    {G : ℝ × PolarPoint → ℝ} {Θ : PolarPoint → ℝ} {θ₀ : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ q : ℝ, Θ (q, 0) = θ₀)
    (hflow : ∀ q t : ℝ,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    (q₀ t : ℝ) :
    HasDerivAt (fun q => Θ (q, t))
      (circleParameterTrajectoryDerivative G Θ (q₀, t)) q₀ := by
  have hG₀ : ContDiff ℝ ∞ (fun p : PolarPoint => G (q₀, p)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  let A : PolarPoint → ℝ := fun p =>
    circleSpeedSecant (fun x => G (q₀, x)) (p.2, (Θ (q₀, p.2), Θ p))
  let B : PolarPoint → ℝ := fun p =>
    circleParameterSpeedSecant G q₀ (p.1, (p.2, Θ p))
  have hA : Continuous A :=
    (contDiff_circleSpeedSecant hG₀).continuous.comp
      (continuous_snd.prodMk
        ((hΘ.comp (continuous_const.prodMk continuous_snd)).prodMk hΘ))
  have hB : Continuous B :=
    (contDiff_circleParameterSpeedSecant hG q₀).continuous.comp
      (continuous_fst.prodMk (continuous_snd.prodMk hΘ))
  let R : ℝ → ℝ := fun q =>
    Real.exp (∫ r in (0 : ℝ)..t, A (q, r)) *
      ∫ s in (0 : ℝ)..t, Real.exp (-(∫ r in (0 : ℝ)..s, A (q, r))) * B (q, s)
  have hdiff (q : ℝ) : Θ (q, t) - Θ (q₀, t) = (q - q₀) * R q := by
    have hdy (r : ℝ) :
        HasDerivAt (fun s => Θ (q, s) - Θ (q₀, s))
          (A (q, r) * (Θ (q, r) - Θ (q₀, r)) + (q - q₀) * B (q, r)) r := by
      apply ((hflow q r).sub (hflow q₀ r)).congr_deriv
      have hangle := circleSpeed_sub_eq_secant hG₀ r (Θ (q₀, r)) (Θ (q, r))
      have hparameter := circleSpeed_parameter_sub_eq_secant hG q₀ q (r, Θ (q, r))
      change G (q, (r, Θ (q, r))) - G (q₀, (r, Θ (q₀, r))) =
        circleSpeedSecant (fun x => G (q₀, x)) (r, (Θ (q₀, r), Θ (q, r))) *
          (Θ (q, r) - Θ (q₀, r)) +
          (q - q₀) * circleParameterSpeedSecant G q₀ (q, (r, Θ (q, r)))
      calc
        G (q, (r, Θ (q, r))) - G (q₀, (r, Θ (q₀, r))) =
            (G (q, (r, Θ (q, r))) - G (q₀, (r, Θ (q, r)))) +
              (G (q₀, (r, Θ (q, r))) - G (q₀, (r, Θ (q₀, r)))) := by ring
        _ = _ := by rw [hparameter, hangle]; ring
    have hfactor :
        (∫ s in (0 : ℝ)..t, Real.exp (-(∫ r in (0 : ℝ)..s, A (q, r))) *
          ((q - q₀) * B (q, s))) =
        (q - q₀) * ∫ s in (0 : ℝ)..t,
          Real.exp (-(∫ r in (0 : ℝ)..s, A (q, r))) * B (q, s) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      ring
    have he := scalar_inhomogeneousODE_eq_exp_mul_global
      (hA.comp (continuous_const.prodMk continuous_id))
      (continuous_const.mul (hB.comp (continuous_const.prodMk continuous_id))) hdy 0 t
    change Θ (q, t) - Θ (q₀, t) =
      Real.exp (∫ r in (0 : ℝ)..t, A (q, r)) *
        (Θ (q, 0) - Θ (q₀, 0) +
          ∫ s in (0 : ℝ)..t, Real.exp (-∫ r in (0 : ℝ)..s, A (q, r)) *
            ((q - q₀) * B (q, s))) at he
    simp only [hinit, sub_self, zero_add, hfactor] at he
    dsimp only [R]
    rw [he]
    ring
  have hprimitive : Continuous
      (fun p : PolarPoint => ∫ r in (0 : ℝ)..p.2, A (p.1, r)) :=
    (contDiff_parametric_primitive_nat (n := 0) (contDiff_zero.mpr hA) 0).continuous
  have hweighted : Continuous
      (fun p : PolarPoint => Real.exp (-(∫ r in (0 : ℝ)..p.2, A (p.1, r))) * B p) :=
    (Real.continuous_exp.comp hprimitive.neg).mul hB
  have hR : Continuous R :=
    (Real.continuous_exp.comp (continuous_parametric_intervalIntegral hA 0 t)).mul
      (continuous_parametric_intervalIntegral hweighted 0 t)
  have hd : HasDerivAt (fun q => Θ (q, t)) (R q₀) q₀ :=
    hasDerivAt_of_continuous_secant_factor hR.continuousAt hdiff
  have hAI (s : ℝ) : (∫ r in (0 : ℝ)..s, A (q₀, r)) =
      ∫ r in (0 : ℝ)..s, circleSpeedAngleDeriv G (q₀, (r, Θ (q₀, r))) := by
    apply intervalIntegral.integral_congr
    intro r _
    change circleSpeedSecant (fun x => G (q₀, x)) (r, (Θ (q₀, r), Θ (q₀, r))) =
      circleSpeedAngleDeriv G (q₀, (r, Θ (q₀, r)))
    rw [circleSpeedSecant_diagonal]
    exact (circleSpeedAngleDeriv_eq_angularPartial hG q₀ (r, Θ (q₀, r))).symm
  apply hd.congr_deriv
  dsimp only [R, circleParameterTrajectoryDerivative]
  rw [hAI t]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change Real.exp (-(∫ r in (0 : ℝ)..s, A (q₀, r))) * B (q₀, s) =
    Real.exp (-(∫ r in (0 : ℝ)..s,
      circleSpeedAngleDeriv G (q₀, (r, Θ (q₀, r))))) *
        circleSpeedParameterDeriv G (q₀, (s, Θ (q₀, s)))
  rw [hAI s]
  change Real.exp (-(∫ r in (0 : ℝ)..s,
      circleSpeedAngleDeriv G (q₀, (r, Θ (q₀, r))))) *
        circleParameterSpeedSecant G q₀ (q₀, (s, Θ (q₀, s))) = _
  rw [circleParameterSpeedSecant_diagonal]

/-- The first-variation expression is as smooth as the actual trajectory
values.  The integral operators preserve each finite order. -/
theorem contDiff_circleParameterTrajectoryDerivative
    {G : ℝ × PolarPoint → ℝ} {Θ : PolarPoint → ℝ} {n : ℕ}
    (hG : ContDiff ℝ ∞ G) (hΘ : ContDiff ℝ n Θ) :
    ContDiff ℝ n (circleParameterTrajectoryDerivative G Θ) := by
  have hK : ContDiff ℝ n (fun p : PolarPoint =>
      circleSpeedAngleDeriv G (p.1, (p.2, Θ p))) :=
    (contDiff_infty.mp (contDiff_circleSpeedAngleDeriv hG) n).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk hΘ))
  have hQ : ContDiff ℝ n (fun p : PolarPoint =>
      circleSpeedParameterDeriv G (p.1, (p.2, Θ p))) :=
    (contDiff_infty.mp (contDiff_circleSpeedParameterDeriv hG) n).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk hΘ))
  have hI := contDiff_parametric_primitive_nat hK (0 : ℝ)
  have hF : ContDiff ℝ n (fun p : PolarPoint =>
      Real.exp (-(∫ r in (0 : ℝ)..p.2,
        circleSpeedAngleDeriv G (p.1, (r, Θ (p.1, r))))) *
          circleSpeedParameterDeriv G (p.1, (p.2, Θ p))) :=
    (Real.contDiff_exp.comp hI.neg).mul hQ
  exact (Real.contDiff_exp.comp hI).mul (contDiff_parametric_primitive_nat hF 0)

/-- All finite parameter and time derivatives are derived from the actual
global time ODE.  The induction assumes only the lower finite regularity
proved at its preceding step. -/
theorem contDiff_globalCircleParameterTrajectory
    {G : ℝ × PolarPoint → ℝ} {Θ : PolarPoint → ℝ} {θ₀ : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ q : ℝ, Θ (q, 0) = θ₀)
    (hflow : ∀ q t : ℝ,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t) :
    ContDiff ℝ ∞ Θ := by
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hΘ
  | succ n ih =>
    have hparameter : ContDiff ℝ n (circleParameterTrajectoryDerivative G Θ) :=
      contDiff_circleParameterTrajectoryDerivative hG ih
    have htime : ContDiff ℝ n (fun p : PolarPoint => G (p.1, (p.2, Θ p))) :=
      (contDiff_infty.mp hG n).comp (contDiff_fst.prodMk (contDiff_snd.prodMk ih))
    exact contDiff_succ_of_coordinate_hasDerivAt hparameter htime
      (globalCircleParameterTrajectory_hasDerivAt_parameter hG hΘ hinit hflow) hflow

/-- A smooth time change of the supplied compact-interval parameter family
is genuinely jointly smooth in parameter and new time.  Individual time
continuity is the only continuity hypothesis on the trajectory family. -/
theorem contDiff_circleParameterTrajectory_timeChange
    {G : ℝ × PolarPoint → ℝ} {Θ : PolarPoint → ℝ} {a b θ₀ P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ q t : ℝ, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (htime : ∀ q : ℝ, ContinuousOn (fun r => Θ (q, r)) (Icc a b))
    (hinit : ∀ q : ℝ, Θ (q, a) = θ₀)
    (hflow : ∀ q t : ℝ, t ∈ Ioo a b →
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (hτzero : τ 0 = a)
    (hτrange : ∀ s : ℝ, τ s ∈ Icc a b) :
    ContDiff ℝ ∞ (fun p : PolarPoint => Θ (p.1, τ p.2)) := by
  let V : ℝ × PolarPoint → ℝ := fun p =>
    deriv τ p.2.1 * G (p.1, (τ p.2.1, p.2.2))
  have hV : ContDiff ℝ ∞ V :=
    ((contDiff_infty_iff_deriv.mp hτ).2.comp contDiff_snd.fst).mul
      (hG.comp (contDiff_fst.prodMk
        ((hτ.comp contDiff_snd.fst).prodMk contDiff_snd.snd)))
  have hcontinuous : Continuous (fun p : PolarPoint => Θ (p.1, τ p.2)) :=
    (circleParameterTrajectory_continuousOn hG hP hperiod htime hinit hflow).comp_continuous
      (continuous_fst.prodMk (hτ.continuous.comp continuous_snd))
      (fun p => ⟨mem_univ p.1, hτrange p.2⟩)
  have hinitial (q : ℝ) : Θ (q, τ 0) = θ₀ := by rw [hτzero, hinit q]
  have htime' (q s : ℝ) : HasDerivAt (fun r => Θ (q, τ r))
      (V (q, (s, Θ (q, τ s)))) s :=
    hasDerivAt_timeChange_classicalTrajectory ((hτrange 0).1.trans (hτrange 0).2)
      (hG.continuous.comp (continuous_const.prodMk continuous_id))
      (htime q) (fun r hr => hflow q r hr) hτrange
      ((hτ.differentiable (by simp) s).hasDerivAt)
  exact contDiff_globalCircleParameterTrajectory hV hcontinuous hinitial htime'

/-- Every actual closed-interval time slice is smooth in the scalar speed
parameter, including the two endpoint slices. -/
theorem circleParameterTrajectory_contDiff_parameter
    {G : ℝ × PolarPoint → ℝ} {Θ : PolarPoint → ℝ} {a b θ₀ P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ q t : ℝ, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (htime : ∀ q : ℝ, ContinuousOn (fun r => Θ (q, r)) (Icc a b))
    (hinit : ∀ q : ℝ, Θ (q, a) = θ₀)
    (hflow : ∀ q t : ℝ, t ∈ Ioo a b →
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (fun q => Θ (q, t)) := by
  have hsmooth := contDiff_circleParameterTrajectory_timeChange hG hP hperiod htime hinit hflow
    (contDiff_circleFlowCompactTime a b) (circleFlowCompactTime_zero a b)
    (circleFlowCompactTime_mem (ht.1.trans ht.2))
  obtain ⟨s, _, hs⟩ := circleFlowCompactTime_surjOn a b ht
  have hslice : ContDiff ℝ ∞ (fun q => Θ (q, circleFlowCompactTime a b s)) :=
    hsmooth.comp (contDiff_id.prodMk contDiff_const)
  simpa only [hs] using hslice

end ContinuousFlexibility.Analysis
