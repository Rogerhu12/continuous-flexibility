import ContinuousFlexibility.Radial.CentralRadialWeakTransport

/-!
# Radial tests whose support can approach zero

`support v ⊆ (0,∞)` does not imply the same inclusion for `tsupport v`.
The Gaussian in the actual radius controls the pullback of these larger
tests. In mode two the already proved compact core then extends the weak
pairing to their genuine whole-line differential graph pairs.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory Polynomial
open scoped Topology ContDiff InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private def LeftPolyBound (f : ℝ → ℝ) : Prop :=
  ∃ p : ℝ[X], (∀ x : ℝ, 0 ≤ p.eval x) ∧ ∀ x : ℝ, x ≤ 0 → |f x| ≤ p.eval x

private def LeftGaussianBound (f : ℝ → ℝ) : Prop :=
  ∃ p : ℝ[X], (∀ x : ℝ, 0 ≤ p.eval x) ∧
    ∀ x : ℝ, x ≤ 0 → |f x| ≤ p.eval x * oscillatorGround 1 x

private theorem lpb_bound {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x : ℝ, x ≤ 0 → |f x| ≤ B) : LeftPolyBound f :=
  ⟨C B, by simpa only [eval_C] using (fun _ : ℝ => hB), by simpa only [eval_C] using hf⟩

private theorem lpb_const (a : ℝ) : LeftPolyBound (fun _ : ℝ => a) :=
  lpb_bound (abs_nonneg a) (fun _ _ => le_rfl)

private theorem lpb_add {f g : ℝ → ℝ} (hf : LeftPolyBound f) (hg : LeftPolyBound g) :
    LeftPolyBound (fun x => f x + g x) := by
  rcases hf with ⟨p, hp, hfp⟩
  rcases hg with ⟨q, hq, hgq⟩
  refine ⟨p + q, fun x => by simpa only [eval_add] using add_nonneg (hp x) (hq x), ?_⟩
  intro x hx
  exact (abs_add_le _ _).trans (by simpa only [eval_add] using add_le_add (hfp x hx) (hgq x hx))

private theorem lpb_neg {f : ℝ → ℝ} (hf : LeftPolyBound f) : LeftPolyBound (fun x => -f x) := by
  rcases hf with ⟨p, hp, hfp⟩
  exact ⟨p, hp, fun x hx => by simpa only [abs_neg] using hfp x hx⟩

private theorem lpb_sub {f g : ℝ → ℝ} (hf : LeftPolyBound f) (hg : LeftPolyBound g) :
    LeftPolyBound (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using lpb_add hf (lpb_neg hg)

private theorem lpb_mul {f g : ℝ → ℝ} (hf : LeftPolyBound f) (hg : LeftPolyBound g) :
    LeftPolyBound (fun x => f x * g x) := by
  rcases hf with ⟨p, hp, hfp⟩
  rcases hg with ⟨q, hq, hgq⟩
  refine ⟨p * q, fun x => by simpa only [eval_mul] using mul_nonneg (hp x) (hq x), ?_⟩
  intro x hx
  simpa only [abs_mul, eval_mul] using mul_le_mul (hfp x hx) (hgq x hx) (abs_nonneg _) (hp x)

private theorem lpb_xsq : LeftPolyBound (fun x : ℝ => x ^ 2) := by
  refine ⟨X ^ 2, fun x => by simp only [eval_pow, eval_X]; positivity, ?_⟩
  intro x _
  simpa only [eval_pow, eval_X, abs_of_nonneg (sq_nonneg x)] using (le_rfl : x ^ 2 ≤ x ^ 2)

private theorem lpb_x : LeftPolyBound (fun x : ℝ => x) := by
  refine ⟨1 + X ^ 2, fun x => by simp only [eval_add, eval_one, eval_pow, eval_X]; positivity, ?_⟩
  intro x _
  simp only [eval_add, eval_one, eval_pow, eval_X]
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

private theorem lpb_nu : LeftPolyBound centralRadiusLogDerivative := by
  refine ⟨C (2 * centralRadiusWeightConstant) * (1 + X ^ 2), ?_, ?_⟩
  · intro x
    simp only [eval_mul, eval_C, eval_add, eval_one, eval_pow, eval_X]
    exact mul_nonneg (mul_nonneg (by norm_num) centralRadiusWeightConstant_pos.le)
      (add_nonneg zero_le_one (sq_nonneg x))
  · intro x _
    simp only [eval_mul, eval_C, eval_add, eval_one, eval_pow, eval_X]
    have hx : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
    have hg := centralRadiusLogDerivative_norm_le_linear x
    rw [Real.norm_eq_abs] at hg
    calc
      _ ≤ centralRadiusWeightConstant * (1 + |x|) := hg
      _ ≤ centralRadiusWeightConstant * (2 * (1 + x ^ 2)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg x]) centralRadiusWeightConstant_pos.le
      _ = _ := by ring

private theorem lpb_radius : LeftPolyBound centralRadius :=
  lpb_bound (centralRadius_pos 0).le (fun x hx => by
    rw [abs_of_pos (centralRadius_pos x)]
    exact strictMono_centralRadius.monotone hx)

private theorem lgb_factor {f g b : ℝ → ℝ} (hg : LeftGaussianBound g)
    (hb : LeftPolyBound b) (heq : ∀ x, f x = g x * b x) : LeftGaussianBound f := by
  rcases hg with ⟨p, hp, hgp⟩
  rcases hb with ⟨q, hq, hbq⟩
  refine ⟨p * q, fun x => by simpa only [eval_mul] using mul_nonneg (hp x) (hq x), ?_⟩
  intro x hx
  rw [heq, abs_mul, eval_mul]
  calc
    _ ≤ (p.eval x * oscillatorGround 1 x) * q.eval x :=
      mul_le_mul (hgp x hx) (hbq x hx) (abs_nonneg _) (mul_nonneg (hp x) (oscillatorGround_pos 1 x).le)
    _ = _ := by ring

private theorem lgb_density_radius :
    LeftGaussianBound (fun x => centralDensityRoot x * centralRadius x) := by
  have hα : 0 < centralRadiusAlpha := by linarith [centralRadiusAlpha_gt_half]
  refine ⟨C (gaussianLaplaceMoment centralRadiusAlpha 0),
    fun _ => by simpa only [eval_C] using (gaussianLaplaceMoment_pos hα 0).le, ?_⟩
  intro x hx
  rw [abs_of_pos (mul_pos (centralDensityRoot_pos x) (centralRadius_pos x)), eval_C]
  have he : centralDensityRoot x * centralRadius x =
      oscillatorGround 1 x * gaussianLaplaceMoment centralRadiusAlpha x := by
    unfold centralDensityRoot centralRadius
    rw [← mul_assoc, ← exp_add, show -centralRadiusA * x + centralRadiusA * x = 0 by ring,
      exp_zero, one_mul]
    simp only [centralRadiusPsi, gaussianLaplacePsi, oscillatorGround, one_mul, neg_div]
  rw [he]
  have hm := (strictMono_gaussianLaplaceMoment hα).monotone hx
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm (oscillatorGround_pos 1 x).le

private theorem eventually_zero_deriv {f : ℝ → ℝ} (hf : ∀ᶠ x in atTop, f x = 0) :
    ∀ᶠ x in atTop, deriv f x = 0 := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp hf
  filter_upwards [eventually_ge_atTop (M + 1)] with x hx
  have he : f =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
    filter_upwards [Ioi_mem_nhds (show M < x by linarith)] with y hy
    exact hM y hy.le
  simpa only [deriv_const] using he.deriv_eq

private theorem memLp_of_leftGaussian {f : ℝ → ℝ} (hf : Continuous f)
    (hg : LeftGaussianBound f) (hz : ∀ᶠ x in atTop, f x = 0) : MemLp f 2 volume := by
  rcases hg with ⟨p, hp, hfp⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hz
  obtain ⟨N, hN⟩ := exists_nat_ge M
  let η : ℝ → ℝ := fun x => scaledOscillatorCutoff N x * f x
  have hη : MemLp η 2 volume :=
    ((contDiff_scaledOscillatorCutoff N).continuous.mul hf).memLp_of_hasCompactSupport
      (scaledOscillatorCutoff_hasCompactSupport N).mul_right
  have hG := memLp_polynomialGaussian (by norm_num : (0 : ℝ) < 1) p
  have hD := hG.add hη.norm
  apply hD.of_le_mul hf.aestronglyMeasurable (c := 1)
  filter_upwards with x
  have hpx : 0 ≤ polynomialGaussian 1 p x := mul_nonneg (hp x) (oscillatorGround_pos 1 x).le
  change ‖f x‖ ≤ 1 * ‖polynomialGaussian 1 p x + ‖η x‖‖
  rw [one_mul, Real.norm_of_nonneg (add_nonneg hpx (norm_nonneg _)), Real.norm_eq_abs]
  by_cases hx : x ≤ 0
  · exact (hfp x hx).trans (by
      dsimp only [polynomialGaussian]
      exact le_add_of_nonneg_right (norm_nonneg (η x)))
  · by_cases hxN : x ≤ (N : ℝ)
    · have hχ : scaledOscillatorCutoff N x = 1 := by
        apply oscillatorCutoff_eq_one
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1),
          div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1), one_mul]
        rw [abs_of_pos (lt_of_not_ge hx)]
        linarith
      have he : η x = f x := by dsimp [η]; rw [hχ, one_mul]
      rw [he, Real.norm_eq_abs]
      linarith
    · rw [hM x (le_trans hN (le_of_lt (lt_of_not_ge hxN))), abs_zero]
      positivity

theorem positive_support_test_elementary_bounds {v : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) (hp : Function.support v ⊆ Ioi 0) :
    v 0 = 0 ∧ ∃ B : ℝ, 1 ≤ B ∧
      (∀ r : ℝ, |deriv v r| ≤ B ∧ |deriv (deriv v) r| ≤ B) ∧
      ∀ r : ℝ, 0 ≤ r → |v r| ≤ B * r := by
  have hv0 : v 0 = 0 := by
    by_contra h
    exact (lt_irrefl (0 : ℝ)) (hp h)
  have h1 := (contDiff_infty_iff_deriv.mp hs).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  obtain ⟨B1, hB1⟩ := hc.deriv.exists_bound_of_continuous h1.continuous
  obtain ⟨B2, hB2⟩ := hc.deriv.deriv.exists_bound_of_continuous h2.continuous
  let B : ℝ := max 1 (max B1 B2)
  have hB : 1 ≤ B := le_max_left _ _
  have hd : ∀ r : ℝ, |deriv v r| ≤ B := by
    intro r
    have hB1r : |deriv v r| ≤ B1 := by simpa only [Real.norm_eq_abs] using hB1 r
    exact hB1r.trans
      ((le_max_left B1 B2).trans (le_max_right 1 (max B1 B2)))
  have hdd : ∀ r : ℝ, |deriv (deriv v) r| ≤ B := by
    intro r
    have hB2r : |deriv (deriv v) r| ≤ B2 := by simpa only [Real.norm_eq_abs] using hB2 r
    exact hB2r.trans
      ((le_max_right B1 B2).trans (le_max_right 1 (max B1 B2)))
  refine ⟨hv0, B, hB, fun r => ⟨hd r, hdd r⟩, ?_⟩
  intro r hr
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := r)
    (fun x _ => (hs.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
    (fun x _ => by simpa only [Real.norm_eq_abs] using hd x)
    r ⟨hr, le_rfl⟩
  simpa only [hv0, sub_zero, Real.norm_eq_abs] using hh

private def flatRatio (v : ℝ → ℝ) (x : ℝ) : ℝ := v (centralRadius x) / centralRadius x

private def flatFirstFactor (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  (-centralRadiusA) * flatRatio v x + deriv v (centralRadius x) * centralRadiusLogDerivative x

private def flatSecondFactor (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  centralRadiusA ^ 2 * flatRatio v x -
    (2 * centralRadiusA) * (deriv v (centralRadius x) * centralRadiusLogDerivative x) +
    (deriv (deriv v) (centralRadius x) * centralRadius x) *
      (centralRadiusLogDerivative x * centralRadiusLogDerivative x) +
    deriv v (centralRadius x) *
      ((2 * centralRadiusA) * centralRadiusLogDerivative x + x ^ 2 - centralOscillatorA)

private theorem radius_deriv_nu (x : ℝ) :
    deriv centralRadius x = centralRadiusLogDerivative x * centralRadius x := by
  unfold centralRadiusLogDerivative
  exact (div_mul_cancel₀ _ (centralRadius_pos x).ne').symm

private theorem radius_second_nu (x : ℝ) :
    deriv (deriv centralRadius) x = centralRadius x *
      (2 * centralRadiusA * centralRadiusLogDerivative x + x ^ 2 - centralOscillatorA) := by
  have h := centralRadius_ode x
  rw [radius_deriv_nu] at h
  nlinarith only [h]

private theorem flat_pullback_factor (v : ℝ → ℝ) (x : ℝ) :
    centralRadialTestPullback v x =
      (centralDensityRoot x * centralRadius x) * flatRatio v x := by
  unfold centralRadialTestPullback flatRatio
  field_simp [(centralRadius_pos x).ne']

private theorem flat_pullback_deriv_raw {v : ℝ → ℝ} (hs : ContDiff ℝ ∞ v) :
    deriv (centralRadialTestPullback v) = fun x =>
      (-centralRadiusA) * centralRadialTestPullback v x +
        centralDensityRoot x * deriv v (centralRadius x) * deriv centralRadius x := by
  funext x
  have hd := (hasDerivAt_centralDensityRoot x).mul
    (((hs.differentiable (by simp) _).hasDerivAt).comp x
      ((contDiff_centralRadius.differentiable (by simp) x).hasDerivAt))
  change HasDerivAt (centralRadialTestPullback v) _ x at hd
  rw [hd.deriv]
  unfold centralRadialTestPullback
  simp only [Function.comp_apply]
  ring

private theorem flat_pullback_deriv_factor {v : ℝ → ℝ} (hs : ContDiff ℝ ∞ v) (x : ℝ) :
    deriv (centralRadialTestPullback v) x =
      (centralDensityRoot x * centralRadius x) * flatFirstFactor v x := by
  rw [flat_pullback_deriv_raw hs]
  dsimp only
  rw [flat_pullback_factor, radius_deriv_nu]
  unfold flatFirstFactor
  ring

private theorem flat_pullback_second_factor {v : ℝ → ℝ} (hs : ContDiff ℝ ∞ v) (x : ℝ) :
    deriv (deriv (centralRadialTestPullback v)) x =
      (centralDensityRoot x * centralRadius x) * flatSecondFactor v x := by
  have hR := (contDiff_centralRadius.differentiable (by simp) x).hasDerivAt
  have hv := ((hs.differentiable (by simp) _).hasDerivAt).comp x hR
  have h1 := (contDiff_infty_iff_deriv.mp hs).2
  have hv1 := ((h1.differentiable (by simp) _).hasDerivAt).comp x hR
  have hR1 := ((contDiff_infty_iff_deriv.mp contDiff_centralRadius).2.differentiable (by simp) x).hasDerivAt
  have hφ := (hasDerivAt_centralDensityRoot x).mul hv
  have ht := (((hasDerivAt_centralDensityRoot x).mul hv1).mul hR1)
  have hd := (hφ.const_mul (-centralRadiusA)).add ht
  change HasDerivAt (fun y => (-centralRadiusA) * centralRadialTestPullback v y +
    centralDensityRoot y * deriv v (centralRadius y) * deriv centralRadius y) _ x at hd
  rw [flat_pullback_deriv_raw hs, hd.deriv]
  simp only [flatSecondFactor, flatRatio, Function.comp_apply, Pi.mul_apply]
  simp only [radius_deriv_nu, radius_second_nu]
  field_simp [(centralRadius_pos x).ne']
  ring

private theorem flat_pullback_H_factor {v : ℝ → ℝ} (hs : ContDiff ℝ ∞ v) (j x : ℝ) :
    liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot (centralRadialTestPullback v) x =
      (centralDensityRoot x * centralRadius x) *
        (-flatSecondFactor v x +
          (j ^ 2 * x ^ 2 + (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA)) * flatRatio v x) := by
  rw [central_liouvilleSchrodinger, flat_pullback_second_factor hs, flat_pullback_factor]
  ring

private theorem flat_factor_poly_bounds {v : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ r : ℝ, 0 ≤ r → |v r| ≤ B * r)
    (hd : ∀ r : ℝ, |deriv v r| ≤ B ∧ |deriv (deriv v) r| ≤ B) :
    LeftPolyBound (flatRatio v) ∧ LeftPolyBound (flatFirstFactor v) ∧
      LeftPolyBound (flatSecondFactor v) := by
  have hr : LeftPolyBound (flatRatio v) := lpb_bound hB (fun x _ => by
    unfold flatRatio
    rw [abs_div, abs_of_pos (centralRadius_pos x)]
    exact (div_le_iff₀ (centralRadius_pos x)).mpr (hv _ (centralRadius_pos x).le))
  have h1 : LeftPolyBound (fun x => deriv v (centralRadius x)) :=
    lpb_bound hB (fun x _ => (hd _).1)
  have h2 : LeftPolyBound (fun x => deriv (deriv v) (centralRadius x)) :=
    lpb_bound hB (fun x _ => (hd _).2)
  refine ⟨hr, lpb_add (lpb_mul (lpb_const _) hr) (lpb_mul h1 lpb_nu), ?_⟩
  exact lpb_add
    (lpb_add
      (lpb_sub (lpb_mul (lpb_const _) hr) (lpb_mul (lpb_const _) (lpb_mul h1 lpb_nu)))
      (lpb_mul (lpb_mul h2 lpb_radius) (lpb_mul lpb_nu lpb_nu)))
    (lpb_mul h1 (lpb_sub (lpb_add (lpb_mul (lpb_const _) lpb_nu) lpb_xsq) (lpb_const _)))

private theorem flat_pullback_eventually_zero {v : ℝ → ℝ} (hc : HasCompactSupport v) :
    ∀ᶠ x in atTop, centralRadialTestPullback v x = 0 := by
  obtain ⟨M, hM⟩ := hc.bddAbove
  filter_upwards [tendsto_centralRadius_atTop (eventually_ge_atTop (M + 1))] with x hx
  change M + 1 ≤ centralRadius x at hx
  have hv : v (centralRadius x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := hM h
    linarith
  simp only [centralRadialTestPullback, hv, mul_zero]

/-- These pullbacks have genuine Gaussian L² tails, even if the closed
support of the radial test meets zero. -/
theorem centralRadial_flat_test_energy {v : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) (hp : Function.support v ⊆ Ioi 0) :
    OscillatorEnergyDomain (centralRadialTestPullback v) ∧
      ∀ j : ℝ, MemLp
        (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot (centralRadialTestPullback v)) 2 volume := by
  obtain ⟨_, B, hB, hd, hv⟩ := positive_support_test_elementary_bounds hs hc hp
  obtain ⟨hr, h1, h2⟩ := flat_factor_poly_bounds (by linarith : 0 ≤ B) hv hd
  have hφ := contDiff_centralRadialTestPullback hs
  have hz := flat_pullback_eventually_zero hc
  have hz1 := eventually_zero_deriv hz
  have hz2 := eventually_zero_deriv hz1
  have hφG := lgb_factor lgb_density_radius hr (flat_pullback_factor v)
  have h1G := lgb_factor lgb_density_radius h1 (flat_pullback_deriv_factor hs)
  have hxG := lgb_factor hφG lpb_x (fun x => mul_comm _ _)
  have hL0 := memLp_of_leftGaussian hφ.continuous hφG hz
  have hL1 := memLp_of_leftGaussian (contDiff_infty_iff_deriv.mp hφ).2.continuous h1G hz1
  have hLx := memLp_of_leftGaussian (continuous_id.mul hφ.continuous) hxG
    (hz.mono (fun x hx => by
      change x * centralRadialTestPullback v x = 0
      rw [hx, mul_zero]))
  refine ⟨⟨hφ.of_le (by simp), hL0, hL1, hLx⟩, ?_⟩
  intro j
  have hV : LeftPolyBound (fun x : ℝ => j ^ 2 * x ^ 2 +
      (centralRadiusA ^ 2 - j ^ 2 * centralOscillatorA)) :=
    lpb_add (lpb_mul (lpb_const _) lpb_xsq) (lpb_const _)
  have hHG := lgb_factor lgb_density_radius (lpb_add (lpb_neg h2) (lpb_mul hV hr))
    (flat_pullback_H_factor hs j)
  apply memLp_of_leftGaussian (contDiff_centralExpression hφ j).continuous hHG
  filter_upwards [hz, hz2] with x hx hx2
  rw [central_liouvilleSchrodinger, hx, hx2]
  ring

private theorem flat_radialJacobi {v : ℝ → ℝ} (hs : ContDiff ℝ ∞ v) (j c x : ℝ) :
    radialJacobi (j ^ 2) (centralRadialProfile c) v (centralRadius x) =
      -(c * centralDensityRoot x / deriv centralRadius x) *
        liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot (centralRadialTestPullback v) x := by
  have he : v =ᶠ[𝓝 (centralRadius x)] centralRadialHeight (centralRadialTestPullback v) := by
    filter_upwards [Ioi_mem_nhds (centralRadius_pos x)] with r hr
    unfold centralRadialHeight centralRadialTestPullback
    rw [centralRadius_modelCoordinate hr]
    field_simp [(centralDensityRoot_pos (centralModelCoordinate r)).ne']
  have hf : (fun r => centralRadialProfile c r * deriv v r) =ᶠ[𝓝 (centralRadius x)]
      (fun r => centralRadialProfile c r * deriv (centralRadialHeight (centralRadialTestPullback v)) r) := by
    filter_upwards [he.deriv] with r hr
    rw [hr]
  calc
    _ = radialJacobi (j ^ 2) (centralRadialProfile c)
        (centralRadialHeight (centralRadialTestPullback v)) (centralRadius x) := by
      unfold radialJacobi
      rw [hf.deriv_eq, he.eq_of_nhds]
    _ = _ := radialJacobi_centralRadialHeight (contDiff_centralRadialTestPullback hs) j c x

private theorem radial_energy_pairing_two (h F : HermiteL2)
    (hw : CentralRadialCompactWeakEquation 2 h F) {φ : ℝ → ℝ}
    (hφ : OscillatorEnergyDomain φ)
    (hH : MemLp (liouvilleSchrodinger (2 ^ 2) centralRadius centralDensityRoot φ) 2 volume)
    (hν : MemLp (fun x => centralRadiusLogDerivative x * φ x) 2 volume) :
    ⟪centralRadialInverseWeight h,
      hH.toLp (liouvilleSchrodinger (2 ^ 2) centralRadius centralDensityRoot φ)⟫_ℝ =
      12 * ⟪F, hν.toLp (fun x => centralRadiusLogDerivative x * φ x)⟫_ℝ := by
  let L : (HermiteL2 × HermiteL2) →L[ℝ] ℝ :=
    (innerSL ℝ (centralRadialInverseWeight h)).comp (ContinuousLinearMap.snd ℝ HermiteL2 HermiteL2) -
      (12 : ℝ) • (innerSL ℝ F).comp centralRadialTwoGraphWeight
  have hcore : centralCompactSmoothGraph 2 ≤ L.ker := by
    intro p hp
    rcases (mem_centralCompactSmoothGraph 2 p).mp hp with ⟨χ, hs, hc, rfl⟩
    change ⟪centralRadialInverseWeight h, _⟫_ℝ - 12 * ⟪F, centralRadialTwoGraphWeight _⟫_ℝ = 0
    rw [centralRadialTwoGraphWeight_test χ hs hc]
    exact sub_eq_zero.mpr (hw χ hs hc)
  have hclosed := (centralCompactSmoothGraph 2).topologicalClosure_minimal hcore L.isClosed_ker
  rw [centralCompactSmoothGraph_closure (by norm_num : (0 : ℝ) < 2)] at hclosed
  let p : HermiteL2 × HermiteL2 :=
    (hφ.2.1.toLp φ, hH.toLp (liouvilleSchrodinger (2 ^ 2) centralRadius centralDensityRoot φ))
  have hp : p ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2) := central_smooth_energy_graph _ hφ hH
  have hweight := centralRadialInverseWeight_hasWeight (centralRadialTwoGraphWeight p)
  rw [centralRadialInverseWeight_twoGraphWeight p hp] at hweight
  have hactual : HasCentralRadialWeightL2 p.1 (hν.toLp _) := by
    filter_upwards [hφ.2.1.coeFn_toLp, hν.coeFn_toLp] with x hx hy
    rw [hy, hx]
  have he := hweight.unique hactual
  have hl := hclosed hp
  change ⟪centralRadialInverseWeight h, p.2⟫_ℝ - 12 * ⟪F, centralRadialTwoGraphWeight p⟫_ℝ = 0 at hl
  rw [he] at hl
  exact sub_eq_zero.mp hl

private theorem flat_dr_pairing {c : ℝ} (hc : 0 < c) (j : ℝ)
    (u : CentralRadialHilbert c) {v : ℝ → ℝ} (hs : ContDiff ℝ ∞ v)
    (hH : MemLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (centralRadialTestPullback v)) 2 volume) :
    IntegrableOn (fun r => u r * (-radialJacobi (j ^ 2) (centralRadialProfile c) v r)) (Ioi 0) ∧
    (∫ r in Ioi 0, u r * (-radialJacobi (j ^ 2) (centralRadialProfile c) v r)) =
      (c / sqrt (12 * c)) * ⟪centralRadialInverseWeight (centralRadialHilbertEquiv hc u),
        hH.toLp (liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot (centralRadialTestPullback v))⟫_ℝ := by
  let h : HermiteL2 := centralRadialHilbertEquiv hc u
  let Hφ : HermiteL2 := hH.toLp _
  let g : ℝ → ℝ := fun r => u r * (-radialJacobi (j ^ 2) (centralRadialProfile c) v r)
  have ht : sqrt (12 * c) ≠ 0 := (sqrt_pos.mpr (mul_pos (by norm_num) hc)).ne'
  have hprod : Integrable (fun x => centralRadialInverseWeight h x * Hφ x) :=
    (Lp.memLp (centralRadialInverseWeight h)).integrable_mul (Lp.memLp Hφ)
  have hae : (fun x => deriv centralRadius x * g (centralRadius x)) =ᵐ[volume]
      (fun x => (c / sqrt (12 * c)) * (centralRadialInverseWeight h x * Hφ x)) := by
    filter_upwards [centralRadialHilbertEquiv_ae hc u, centralRadialInverseWeight_ae h, hH.coeFn_toLp]
      with x hu hq hHx
    change h x = centralRadialAmplitude c x * u (centralRadius x) at hu
    change Hφ x = liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot
      (centralRadialTestPullback v) x at hHx
    change deriv centralRadius x * (u (centralRadius x) *
      (-radialJacobi (j ^ 2) (centralRadialProfile c) v (centralRadius x))) = _
    rw [flat_radialJacobi hs, hq, hu, hHx]
    unfold centralRadialAmplitude
    field_simp [ht, (deriv_centralRadius_pos x).ne', (centralRadiusLogDerivative_pos x).ne']
  have hg : IntegrableOn g (Ioi 0) :=
    (centralRadius_integrable_iff g).mpr ((hprod.const_mul _).congr hae.symm)
  refine ⟨hg, ?_⟩
  change (∫ r in Ioi 0, g r) = (c / sqrt (12 * c)) * ⟪centralRadialInverseWeight h, Hφ⟫_ℝ
  rw [centralRadius_integral_change, integral_congr_ae hae, integral_const_mul, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem flat_spectral_pairing {c : ℝ} (hc : 0 < c) (F : CentralRadialHilbert c)
    (v : ℝ → ℝ)
    (hν : MemLp (fun x => centralRadiusLogDerivative x * centralRadialTestPullback v x) 2 volume) :
    Integrable (fun r => F r * v r) (centralRadialSpectralMeasure c) ∧
    (∫ r, F r * v r ∂centralRadialSpectralMeasure c) = sqrt (12 * c) *
      ⟪centralRadialHilbertEquiv hc F,
        hν.toLp (fun x => centralRadiusLogDerivative x * centralRadialTestPullback v x)⟫_ℝ := by
  let f : HermiteL2 := centralRadialHilbertEquiv hc F
  let wφ : HermiteL2 := hν.toLp _
  let g : ℝ → ℝ := fun r => F r * v r
  have hsq : sqrt (12 * c) ^ 2 = 12 * c := sq_sqrt (mul_pos (by norm_num) hc).le
  have hprod : Integrable (fun x => f x * wφ x) := (Lp.memLp f).integrable_mul (Lp.memLp wφ)
  have hae : (fun x => centralRadialPullbackDensity c x * g (centralRadius x)) =ᵐ[volume]
      (fun x => sqrt (12 * c) * (f x * wφ x)) := by
    filter_upwards [centralRadialHilbertEquiv_ae hc F, hν.coeFn_toLp] with x hF hw
    change f x = centralRadialAmplitude c x * F (centralRadius x) at hF
    change wφ x = centralRadiusLogDerivative x * centralRadialTestPullback v x at hw
    change centralRadialPullbackDensity c x * (F (centralRadius x) * v (centralRadius x)) = _
    rw [hF, hw]
    have hD : centralRadialPullbackDensity c x =
        sqrt (12 * c) ^ 2 * (centralDensityRoot x * centralRadiusLogDerivative x) ^ 2 := by
      rw [hsq]
      rfl
    rw [hD]
    unfold centralRadialAmplitude centralRadialTestPullback
    ring
  have hg : Integrable g (centralRadialSpectralMeasure c) :=
    (centralRadialSpectral_integrable_iff hc g).mpr ((hprod.const_mul _).congr hae.symm)
  refine ⟨hg, ?_⟩
  change (∫ r, g r ∂centralRadialSpectralMeasure c) = sqrt (12 * c) * ⟪f, wφ⟫_ℝ
  rw [centralRadialSpectral_integral_change hc, integral_congr_ae hae, integral_const_mul, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem centralRadial_flat_test_integrable {c : ℝ} (hc : 0 < c)
    (u F : CentralRadialHilbert c) (v : ℝ → ℝ)
    (hs : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (hvp : Function.support v ⊆ Ioi 0) :
    IntegrableOn (fun r => u r * (-radialJacobi 4 (centralRadialProfile c) v r)) (Ioi 0) ∧
      Integrable (fun r => F r * v r) (centralRadialSpectralMeasure c) := by
  obtain ⟨hφ, hH⟩ := centralRadial_flat_test_energy hs hvc hvp
  have hν := memLp_centralRadialWeight hφ.2.1 hφ.2.2.2
  refine ⟨?_, (flat_spectral_pairing hc F v hν).1⟩
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using (flat_dr_pairing hc 2 u hs (hH 2)).1

/-- Larger positive-support tests, including tests flat at zero, have the
same actual mode-two distribution equation and both pairings are integrable. -/
theorem centralRadialDistributionEquation_flat_test {c : ℝ} (hc : 0 < c)
    (u F : CentralRadialHilbert c) (heq : CentralRadialDistributionEquation c 2 u F)
    (v : ℝ → ℝ) (hs : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hvp : Function.support v ⊆ Ioi 0) :
    IntegrableOn (fun r => u r * (-radialJacobi 4 (centralRadialProfile c) v r)) (Ioi 0) ∧
    Integrable (fun r => F r * v r) (centralRadialSpectralMeasure c) ∧
    (∫ r in Ioi 0, u r * (-radialJacobi 4 (centralRadialProfile c) v r)) =
      ∫ r, F r * v r ∂centralRadialSpectralMeasure c := by
  obtain ⟨hφ, hH⟩ := centralRadial_flat_test_energy hs hvc hvp
  have hν := memLp_centralRadialWeight hφ.2.1 hφ.2.2.2
  have hL := flat_dr_pairing hc 2 u hs (hH 2)
  have hR := flat_spectral_pairing hc F v hν
  have hw := (centralRadialDistributionEquation_iff_normalized hc 2 u F).mp heq
  have hp := radial_energy_pairing_two _ _ hw hφ (hH 2) hν
  have ht : sqrt (12 * c) ≠ 0 := (sqrt_pos.mpr (mul_pos (by norm_num) hc)).ne'
  have hscale : (c / sqrt (12 * c)) * 12 = sqrt (12 * c) := by
    have hsq : sqrt (12 * c) ^ 2 = 12 * c :=
      sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hc.le)
    calc
      (c / sqrt (12 * c)) * 12 = (12 * c) / sqrt (12 * c) := by ring
      _ = sqrt (12 * c) := (div_eq_iff ht).mpr (hsq.symm.trans (pow_two _))
  have he : (∫ r in Ioi 0, u r * (-radialJacobi ((2 : ℝ) ^ 2) (centralRadialProfile c) v r)) =
      ∫ r, F r * v r ∂centralRadialSpectralMeasure c := by
    rw [hL.2, hR.2, hp, ← mul_assoc, hscale]
  exact ⟨by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hL.1,
    hR.1, by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using he⟩

/-- Conversion of the spectral pairing to the actual ordinary `dr`
density, with its integrability retained. -/
theorem centralRadial_spectral_pairing_density {c : ℝ} (hc : 0 < c)
    (F : CentralRadialHilbert c) (v : ℝ → ℝ)
    (hFv : Integrable (fun r => F r * v r) (centralRadialSpectralMeasure c)) :
    IntegrableOn (fun r => centralRadialVarpi c r * F r * v r) (Ioi 0) ∧
      (∫ r, F r * v r ∂centralRadialSpectralMeasure c) =
        ∫ r in Ioi 0, centralRadialVarpi c r * F r * v r := by
  have hd := centralRadialVarpi_aemeasurable c
  have hf : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      ENNReal.ofReal (centralRadialVarpi c r) < (⊤ : ENNReal) := by simp
  have he : (fun r => (ENNReal.ofReal (centralRadialVarpi c r)).toReal • (F r * v r))
      =ᵐ[volume.restrict (Ioi 0)] (fun r => centralRadialVarpi c r * F r * v r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [ENNReal.toReal_ofReal (centralRadialVarpi_pos hc hr).le]
    simp only [smul_eq_mul]
    ring
  have hi := (integrable_withDensity_iff_integrable_smul₀' hd hf).mp hFv
  refine ⟨hi.congr he, ?_⟩
  exact (integral_withDensity_eq_integral_toReal_smul₀ hd hf (fun r => F r * v r)).trans
    (integral_congr_ae he)

def CentralRadialFlatDistributionEquation (c : ℝ) (u F : CentralRadialHilbert c) : Prop :=
  ∀ (v : ℝ → ℝ), ContDiff ℝ ∞ v → HasCompactSupport v → Function.support v ⊆ Ioi 0 →
    (∫ r in Ioi 0, u r * (-radialJacobi 4 (centralRadialProfile c) v r)) =
      ∫ r, F r * v r ∂centralRadialSpectralMeasure c

theorem centralRadialDistributionEquation_iff_flat {c : ℝ} (hc : 0 < c)
    (u F : CentralRadialHilbert c) :
    CentralRadialDistributionEquation c 2 u F ↔ CentralRadialFlatDistributionEquation c u F := by
  constructor
  · intro h v hs hvc hvp
    exact (centralRadialDistributionEquation_flat_test hc u F h v hs hvc hvp).2.2
  · intro h v hs hvc hvp
    have he := h v hs hvc (fun r hr => hvp (subset_tsupport v hr))
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using he

end ContinuousFlexibility.Radial
