import ContinuousFlexibility.Analysis.OneHighCircleFlowVariational

/-!
# Actual first parameter variations of classical circle trajectories

Two trajectories with different speeds satisfy an exact inhomogeneous scalar
equation.  Its integrating-factor formula gives their finite difference.
For a jointly continuous parameter family of classical trajectories, taking
the limit of that exact difference quotient proves the true first parameter
derivative.  Neither a parameter derivative of the flow nor its variational
equation is an input.

The scalar parameter can be a line in the original state space.  Application
to N01 still requires the geometric speed estimates, continuity in that
parameter, and the root regularization on a closed time interval.  No
all-order smooth tower or tame estimate for the N01 flow is claimed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

set_option backward.isDefEq.respectTransparency false

/-- Variation of constants for a true inhomogeneous scalar ODE, with
differentiability only in the open interval and continuous endpoint values. -/
theorem scalar_inhomogeneousODE_eq_exp_mul
    {κ F y : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hκ : ContinuousOn κ (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hy : ContinuousOn y (Icc a b))
    (hdy : ∀ t ∈ Ioo a b, HasDerivAt y (κ t * y t + F t) t) :
    y b = Real.exp (∫ r in a..b, κ r) *
      (y a + ∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) * F t) := by
  let K : ℝ → ℝ := fun t => κ (max a (min t b))
  have hK : Continuous K :=
    hκ.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
      (fun t => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)
  have hKeq (t : ℝ) (ht : t ∈ Icc a b) : K t = κ t := by
    dsimp only [K]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hprimitive (t : ℝ) :
      HasDerivAt (fun x => ∫ r in a..x, K r) (K t) t :=
    (hK.integral_hasStrictDerivAt a t).hasDerivAt
  have hprimitive_cont : Continuous (fun x => ∫ r in a..x, K r) :=
    continuous_iff_continuousAt.mpr (fun t => (hprimitive t).continuousAt)
  have hfactor_cont :
      ContinuousOn (fun t => y t * Real.exp (-∫ r in a..t, K r)) (Icc a b) :=
    hy.mul (Real.continuous_exp.comp hprimitive_cont.neg).continuousOn
  have hforcing_cont : ContinuousOn
      (fun t => Real.exp (-∫ r in a..t, K r) * F t) (Icc a b) :=
    (Real.continuous_exp.comp hprimitive_cont.neg).continuousOn.mul hF
  have hfactor_deriv (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun t => y t * Real.exp (-∫ r in a..t, K r))
        (Real.exp (-∫ r in a..t, K r) * F t) t := by
    have hd := (hdy t ht).mul (hprimitive t).neg.exp
    apply hd.congr_deriv
    simp only [Pi.neg_apply]
    rw [hKeq t (Ioo_subset_Icc_self ht)]
    ring
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hfactor_cont hfactor_deriv (hforcing_cont.intervalIntegrable_of_Icc hab)
  have he : y b * Real.exp (-∫ r in a..b, K r) =
      y a + ∫ t in a..b, Real.exp (-∫ r in a..t, K r) * F t := by
    simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one] at hfund
    linarith
  have hint (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ r in a..t, K r) = ∫ r in a..t, κ r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a t := by simpa only [uIcc_of_le ht.1] using hr
    exact hKeq r ⟨hr'.1, hr'.2.trans ht.2⟩
  have hforcing : (∫ t in a..b, Real.exp (-∫ r in a..t, K r) * F t) =
      ∫ t in a..b, Real.exp (-∫ r in a..t, κ r) * F t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change Real.exp (-∫ r in a..t, K r) * F t =
      Real.exp (-∫ r in a..t, κ r) * F t
    rw [hint t (by simpa only [uIcc_of_le hab] using ht)]
  calc
    y b = (y b * Real.exp (-∫ r in a..b, K r)) *
        Real.exp (∫ r in a..b, K r) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = (y a + ∫ t in a..b, Real.exp (-∫ r in a..t, K r) * F t) *
        Real.exp (∫ r in a..b, K r) := by rw [he]
    _ = _ := by rw [hint b ⟨hab, le_rfl⟩, hforcing, mul_comm]

/-- Exact differences of trajectories of two actual speeds.  The forcing
is their speed difference evaluated along the first trajectory. -/
theorem circleTrajectory_twoSpeeds_difference_eq
    {G H : PolarPoint → ℝ} {u v : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (G (t, u t)) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivAt v (H (t, v t)) t) :
    u b - v b =
      Real.exp (∫ r in a..b, circleSpeedSecant H (r, (v r, u r))) *
        (u a - v a + ∫ t in a..b,
          Real.exp (-(∫ r in a..t, circleSpeedSecant H (r, (v r, u r)))) *
            (G (t, u t) - H (t, u t))) := by
  have hκ : ContinuousOn
      (fun r => circleSpeedSecant H (r, (v r, u r))) (Icc a b) :=
    (contDiff_circleSpeedSecant hH).continuous.comp_continuousOn
      (continuousOn_id.prodMk (hv.prodMk hu))
  have hforcing : ContinuousOn (fun t => G (t, u t) - H (t, u t)) (Icc a b) :=
    (hG.continuous.comp_continuousOn (continuousOn_id.prodMk hu)).sub
      (hH.continuous.comp_continuousOn (continuousOn_id.prodMk hu))
  apply scalar_inhomogeneousODE_eq_exp_mul hab hκ hforcing (hu.sub hv)
  intro t ht
  apply ((hdu t ht).sub (hdv t ht)).congr_deriv
  simp only [Pi.sub_apply]
  have hsec := circleSpeed_sub_eq_secant hH t (v t) (u t)
  linarith

/-- The actual derivative of a speed in its scalar parameter.  The input
coordinates are `(parameter, (time, angle))`. -/
def circleSpeedParameterDeriv (G : ℝ × PolarPoint → ℝ) (p : ℝ × PolarPoint) : ℝ :=
  fderiv ℝ G p (1, (0, 0))

theorem circleSpeedParameterDeriv_apply (G : ℝ × PolarPoint → ℝ)
    (p : ℝ × PolarPoint) :
    circleSpeedParameterDeriv G p = fderiv ℝ G p (1, (0, 0)) := rfl

theorem contDiff_circleSpeedParameterDeriv {G : ℝ × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (circleSpeedParameterDeriv G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_circleSpeed_parameterSlice {G : ℝ × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (q : ℝ) (p : PolarPoint) :
    HasDerivAt (fun s => G (s, p)) (circleSpeedParameterDeriv G (q, p)) q :=
  (hG.differentiable (by simp) (q, p)).hasFDerivAt.comp_hasDerivAt q
    ((hasDerivAt_id q).prodMk (hasDerivAt_const q p))

/-- The parameter divided difference defined by actual derivative integration,
including its value at equal parameters. -/
def circleParameterSpeedSecant (G : ℝ × PolarPoint → ℝ) (q₀ : ℝ)
    (p : ℝ × PolarPoint) : ℝ :=
  ∫ s in (0 : ℝ)..1,
    circleSpeedParameterDeriv G (q₀ + (p.1 - q₀) * s, p.2)

theorem contDiff_circleParameterSpeedSecant {G : ℝ × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (q₀ : ℝ) :
    ContDiff ℝ ∞ (circleParameterSpeedSecant G q₀) := by
  have hc : ContDiff ℝ ∞ (fun p : (ℝ × PolarPoint) × ℝ =>
      circleSpeedParameterDeriv G (q₀ + (p.1.1 - q₀) * p.2, p.1.2)) :=
    (contDiff_circleSpeedParameterDeriv hG).comp
      ((contDiff_const.add ((contDiff_fst.fst.sub contDiff_const).mul contDiff_snd)).prodMk
        contDiff_fst.snd)
  exact contDiff_parametric_intervalIntegral hc 0 1

theorem circleParameterSpeedSecant_diagonal (G : ℝ × PolarPoint → ℝ)
    (q₀ : ℝ) (p : PolarPoint) :
    circleParameterSpeedSecant G q₀ (q₀, p) = circleSpeedParameterDeriv G (q₀, p) := by
  simp only [circleParameterSpeedSecant, sub_self, zero_mul, add_zero,
    intervalIntegral.integral_const, sub_zero, one_smul]

theorem circleSpeed_parameter_sub_eq_secant {G : ℝ × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (q₀ q : ℝ) (p : PolarPoint) :
    G (q, p) - G (q₀, p) = circleParameterSpeedSecant G q₀ (q, p) * (q - q₀) := by
  have hc : Continuous (fun s : ℝ => circleSpeedParameterDeriv G (s, p)) :=
    (contDiff_circleSpeedParameterDeriv hG).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hint : (∫ s in q₀..q, circleSpeedParameterDeriv G (s, p)) =
      G (q, p) - G (q₀, p) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_circleSpeed_parameterSlice hG s p)
      (hc.intervalIntegrable q₀ q)
  have hscale := intervalIntegral.smul_integral_comp_mul_add
    (fun s => circleSpeedParameterDeriv G (s, p))
    (a := (0 : ℝ)) (b := 1) (q - q₀) q₀
  calc
    G (q, p) - G (q₀, p) = ∫ s in q₀..q, circleSpeedParameterDeriv G (s, p) := hint.symm
    _ = (q - q₀) * circleParameterSpeedSecant G q₀ (q, p) := by
      simpa only [circleParameterSpeedSecant, smul_eq_mul, mul_zero, zero_add,
        mul_one, sub_add_cancel, add_comm q₀] using hscale.symm
    _ = circleParameterSpeedSecant G q₀ (q, p) * (q - q₀) := mul_comm _ _

/-- The true first parameter derivative of a jointly continuous family of
classical trajectories with a fixed initial value.  The proof takes the
limit of exact finite differences; parameter differentiability is not assumed.
Here `Θ (q,t)` is a trajectory and `G (q,(t,θ))` is its speed. -/
theorem continuousCircleTrajectory_hasDerivAt_parameter
    {G : ℝ × PolarPoint → ℝ} {Θ : PolarPoint → ℝ} {a b θ₀ : ℝ}
    (hab : a ≤ b) (hG : ContDiff ℝ ∞ G)
    (hΘ : ContinuousOn Θ ((univ : Set ℝ) ×ˢ Icc a b))
    (hinit : ∀ q : ℝ, Θ (q, a) = θ₀)
    (hflow : ∀ q : ℝ, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    (q₀ : ℝ) :
    HasDerivAt (fun q => Θ (q, b))
      (Real.exp (∫ t in a..b,
          angularPartial (fun p => G (q₀, p)) (t, Θ (q₀, t))) *
        ∫ t in a..b,
          Real.exp (-(∫ r in a..t,
            angularPartial (fun p => G (q₀, p)) (r, Θ (q₀, r)))) *
              circleSpeedParameterDeriv G (q₀, (t, Θ (q₀, t)))) q₀ := by
  let clamp : ℝ → ℝ := fun r => max a (min r b)
  have hclamp : Continuous clamp :=
    continuous_const.max (continuous_id.min continuous_const)
  have hclamp_mem (r : ℝ) : clamp r ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hclamp_eq (r : ℝ) (hr : r ∈ Icc a b) : clamp r = r := by
    dsimp only [clamp]
    rw [min_eq_left hr.2, max_eq_right hr.1]
  let Ψ : PolarPoint → ℝ := fun p => Θ (p.1, clamp p.2)
  have hΨ : Continuous Ψ :=
    hΘ.comp_continuous (continuous_fst.prodMk (hclamp.comp continuous_snd))
      (fun p => ⟨mem_univ p.1, hclamp_mem p.2⟩)
  have hG₀ : ContDiff ℝ ∞ (fun p : PolarPoint => G (q₀, p)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  let A : PolarPoint → ℝ := fun p =>
    circleSpeedSecant (fun x => G (q₀, x)) (p.2, (Ψ (q₀, p.2), Ψ p))
  let B : PolarPoint → ℝ := fun p =>
    circleParameterSpeedSecant G q₀ (p.1, (p.2, Ψ p))
  have hA : Continuous A :=
    (contDiff_circleSpeedSecant hG₀).continuous.comp
      (continuous_snd.prodMk
        ((hΨ.comp (continuous_const.prodMk continuous_snd)).prodMk hΨ))
  have hB : Continuous B :=
    (contDiff_circleParameterSpeedSecant hG q₀).continuous.comp
      (continuous_fst.prodMk (continuous_snd.prodMk hΨ))
  have hAeq (q t : ℝ) (ht : t ∈ Icc a b) :
      A (q, t) = circleSpeedSecant (fun p => G (q₀, p))
        (t, (Θ (q₀, t), Θ (q, t))) := by
    simp only [A, Ψ, hclamp_eq t ht]
  have hBeq (q t : ℝ) (ht : t ∈ Icc a b) :
      B (q, t) = circleParameterSpeedSecant G q₀ (q, (t, Θ (q, t))) := by
    simp only [B, Ψ, hclamp_eq t ht]
  have htime (q : ℝ) : ContinuousOn (fun t => Θ (q, t)) (Icc a b) :=
    hΘ.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨mem_univ q, ht⟩)
  let R : ℝ → ℝ := fun q =>
    Real.exp (∫ t in a..b, A (q, t)) *
      ∫ t in a..b, Real.exp (-(∫ r in a..t, A (q, r))) * B (q, t)
  have hdiff (q : ℝ) : Θ (q, b) - Θ (q₀, b) = (q - q₀) * R q := by
    have hdy (t : ℝ) (ht : t ∈ Ioo a b) :
        HasDerivAt (fun r => Θ (q, r) - Θ (q₀, r))
          (A (q, t) * (Θ (q, t) - Θ (q₀, t)) + (q - q₀) * B (q, t)) t := by
      apply ((hflow q t ht).sub (hflow q₀ t ht)).congr_deriv
      rw [hAeq q t (Ioo_subset_Icc_self ht), hBeq q t (Ioo_subset_Icc_self ht)]
      have hangle := circleSpeed_sub_eq_secant hG₀ t (Θ (q₀, t)) (Θ (q, t))
      have hparameter := circleSpeed_parameter_sub_eq_secant hG q₀ q (t, Θ (q, t))
      calc
        G (q, (t, Θ (q, t))) - G (q₀, (t, Θ (q₀, t))) =
            (G (q, (t, Θ (q, t))) - G (q₀, (t, Θ (q, t)))) +
              (G (q₀, (t, Θ (q, t))) - G (q₀, (t, Θ (q₀, t)))) := by ring
        _ = _ := by rw [hparameter, hangle]; ring
    have hfactor :
        (∫ t in a..b, Real.exp (-(∫ r in a..t, A (q, r))) * ((q - q₀) * B (q, t))) =
          (q - q₀) * ∫ t in a..b, Real.exp (-(∫ r in a..t, A (q, r))) * B (q, t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    have he := scalar_inhomogeneousODE_eq_exp_mul hab
      (hA.comp (continuous_const.prodMk continuous_id)).continuousOn
      (continuous_const.mul (hB.comp (continuous_const.prodMk continuous_id))).continuousOn
      ((htime q).sub (htime q₀)) hdy
    change Θ (q, b) - Θ (q₀, b) =
      Real.exp (∫ r in a..b, A (q, r)) *
        (Θ (q, a) - Θ (q₀, a) +
          ∫ t in a..b, Real.exp (-∫ r in a..t, A (q, r)) *
            ((q - q₀) * B (q, t))) at he
    simp only [hinit, sub_self, zero_add, hfactor] at he
    dsimp only [R]
    rw [he]
    ring
  have hprimitive : Continuous (fun p : PolarPoint => ∫ r in a..p.2, A (p.1, r)) :=
    (contDiff_parametric_primitive_nat (n := 0) (contDiff_zero.mpr hA) a).continuous
  have hweighted : Continuous
      (fun p : PolarPoint => Real.exp (-(∫ r in a..p.2, A (p.1, r))) * B p) :=
    (Real.continuous_exp.comp hprimitive.neg).mul hB
  have hR : Continuous R :=
    (Real.continuous_exp.comp (continuous_parametric_intervalIntegral hA a b)).mul
      (continuous_parametric_intervalIntegral hweighted a b)
  have hslope : slope (fun q => Θ (q, b)) q₀ =ᶠ[𝓝[≠] q₀] R := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [slope_def_field, hdiff q]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hq)
  have hd : HasDerivAt (fun q => Θ (q, b)) (R q₀) q₀ :=
    hasDerivAt_iff_tendsto_slope.mpr ((tendsto_congr' hslope).mpr
      (hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  have hAI (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ r in a..t, A (q₀, r)) = ∫ r in a..t,
        angularPartial (fun p => G (q₀, p)) (r, Θ (q₀, r)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a t := by simpa only [uIcc_of_le ht.1] using hr
    change A (q₀, r) = angularPartial (fun p => G (q₀, p)) (r, Θ (q₀, r))
    rw [hAeq q₀ r ⟨hr'.1, hr'.2.trans ht.2⟩, circleSpeedSecant_diagonal]
  apply hd.congr_deriv
  dsimp only [R]
  rw [hAI b ⟨hab, le_rfl⟩]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  change Real.exp (-∫ r in a..t, A (q₀, r)) * B (q₀, t) =
    Real.exp (-∫ r in a..t,
      angularPartial (fun p => G (q₀, p)) (r, Θ (q₀, r))) *
        circleSpeedParameterDeriv G (q₀, (t, Θ (q₀, t)))
  rw [hAI t ht', hBeq q₀ t ht', circleParameterSpeedSecant_diagonal]

end ContinuousFlexibility.Analysis
