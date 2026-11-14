module

public import ContinuousFlexibility.Radial.CentralRadiusGrowth
public import ContinuousFlexibility.Radial.GaussianLaplaceLeftBounds
public import ContinuousFlexibility.Radial.CentralModel
public import ContinuousFlexibility.Radial.GaussianLaplaceLeftSymbols

/-!
# Actual left-end central radius asymptotics

The estimates below compare the actual positive Gaussian--Laplace moments,
then apply the comparison to the already constructed logarithmic radius
derivative. The logarithmic height slope is identified by differentiation
of the actual radial height. Right-end estimates are separate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem positive_ratio_error {A0 A1 B0 B1 e0 e1 : ℝ}
    (hA0 : 0 < A0) (hA1 : 0 < A1) (hB0 : 0 < B0)
    (h0 : 0 ≤ 1 - B0 / A0 ∧ 1 - B0 / A0 ≤ e0)
    (h1 : 0 ≤ 1 - B1 / A1 ∧ 1 - B1 / A1 ≤ e1)
    (he0 : e0 ≤ 1 / 2) :
    |B1 / B0 - A1 / A0| ≤ 2 * (A1 / A0) * (e0 + e1) := by
  have hp : 0 < B0 / A0 := div_pos hB0 hA0
  have hhalf : 1 / 2 ≤ B0 / A0 := by linarith [h0.2]
  have hdiff : |B1 / A1 - B0 / A0| ≤ e0 + e1 := by
    apply abs_le.mpr
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  have he : 0 ≤ e0 + e1 := by linarith [h0.1, h0.2, h1.1, h1.2]
  have hratio : 0 ≤ A1 / A0 := (div_pos hA1 hA0).le
  calc
    _ = (A1 / A0) * |B1 / A1 - B0 / A0| / (B0 / A0) := by
      have hid : B1 / B0 - A1 / A0 =
          (A1 / A0) * (B1 / A1 - B0 / A0) / (B0 / A0) := by
        field_simp
      rw [hid, abs_div, abs_mul, abs_of_nonneg hratio, abs_of_pos hp]
    _ ≤ (A1 / A0) * (e0 + e1) / (B0 / A0) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff hratio) hp.le
    _ ≤ _ := by
      apply (div_le_iff₀ hp).mpr
      have hh := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hratio he)
      nlinarith only [hh]

/-- The actual moment quotient has a cubic left-end remainder. The cutoff
`β+1` is explicit and does not depend on a derivative order. -/
theorem gaussianLaplaceRatio_left_error {β L : ℝ} (hβ : 0 < β) (hL : β + 1 ≤ L) :
    |gaussianLaplaceRatio β (-L) - β / (sqrt 2 * L)| ≤
      β * (β + 1) ^ 2 / (sqrt 2 * L ^ 3) := by
  have hLp : 0 < L := by linarith
  have hrate : 0 < sqrt 2 * L := by positivity
  have hA0 := gammaLaplaceMoment_pos hβ hrate
  have hA1 := gammaLaplaceMoment_pos (by linarith : 0 < β + 1) hrate
  have hB0 := gaussianLaplaceMoment_pos hβ (-L)
  have he0 : β * (β + 1) / (4 * L ^ 2) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * L ^ 2)).mpr
    have hs := pow_le_pow_left₀ (by linarith : 0 ≤ β + 1) hL 2
    nlinarith [sq_nonneg (β + 1)]
  have hb := positive_ratio_error hA0 hA1 hB0
    (gaussianLaplaceMoment_left_relative_error hβ hLp)
    (gaussianLaplaceMoment_left_relative_error (by linarith : 0 < β + 1) hLp) he0
  have hgamma : gammaLaplaceMoment (β + 1) (sqrt 2 * L) /
      gammaLaplaceMoment β (sqrt 2 * L) = β / (sqrt 2 * L) := by
    rw [gammaLaplaceMoment_succ hβ hrate, mul_div_cancel_right₀ _ hA0.ne']
  rw [hgamma] at hb
  unfold gaussianLaplaceRatio
  convert hb using 1
  field_simp
  ring

/-- Equation (sc6a), left side, for the actual radius `r`, with an explicit
cubic error and an actual numerical cutoff. -/
theorem centralRadiusLogDerivative_left_error {L : ℝ}
    (hL : centralRadiusAlpha + 1 ≤ L) :
    |centralRadiusLogDerivative (-L) -
      (centralRadiusA + L + centralRadiusAlpha / L)| ≤
      centralRadiusAlpha * (centralRadiusAlpha + 1) ^ 2 / L ^ 3 := by
  have hβ : 0 < centralRadiusAlpha := by linarith [centralRadiusAlpha_gt_half]
  have hLp : 0 < L := by linarith
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have hh := mul_le_mul_of_nonneg_left (gaussianLaplaceRatio_left_error hβ hL) hs.le
  rw [centralRadiusLogDerivative_eq]
  calc
    _ = |sqrt 2 * (gaussianLaplaceRatio centralRadiusAlpha (-L) -
        centralRadiusAlpha / (sqrt 2 * L))| := by
      congr 1
      field_simp
      ring
    _ = sqrt 2 * |gaussianLaplaceRatio centralRadiusAlpha (-L) -
        centralRadiusAlpha / (sqrt 2 * L)| := by rw [abs_mul, abs_of_pos hs]
    _ ≤ sqrt 2 * (centralRadiusAlpha * (centralRadiusAlpha + 1) ^ 2 /
        (sqrt 2 * L ^ 3)) := hh
    _ = _ := by field_simp

private theorem constant_div_pow_tendsto_zero (C : ℝ) (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun L : ℝ => C / L ^ n) atTop (𝓝 0) := by
  have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  simpa only [div_eq_mul_inv, inv_pow, zero_pow hn, mul_zero] using
    (hi.pow n).const_mul C

theorem centralRadiusLogDerivative_left_remainder_tendsto :
    Tendsto (fun L : ℝ => centralRadiusLogDerivative (-L) -
      (centralRadiusA + L + centralRadiusAlpha / L)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun L => norm_nonneg _))
  · exact (eventually_ge_atTop (centralRadiusAlpha + 1)).mono
      (fun L hL => centralRadiusLogDerivative_left_error hL)
  · exact constant_div_pow_tendsto_zero _ 3 (by decide)

theorem centralRadiusLogDerivative_left_sub_tendsto :
    Tendsto (fun L : ℝ => centralRadiusLogDerivative (-L) - L) atTop (𝓝 centralRadiusA) := by
  have ht := centralRadiusLogDerivative_left_remainder_tendsto.add
    ((tendsto_const_nhds (x := centralRadiusA)).add
      (constant_div_pow_tendsto_zero centralRadiusAlpha 1 (by decide)))
  convert ht using 1
  · funext L
    simp only [pow_one]
    ring
  · simp only [zero_add, add_zero]

theorem centralRadiusLogDerivative_left_ratio_tendsto :
    Tendsto (fun L : ℝ => centralRadiusLogDerivative (-L) / L) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add
    (centralRadiusLogDerivative_left_sub_tendsto.mul tendsto_inv_atTop_zero)
  have hs : Tendsto (fun L : ℝ => 1 +
      (centralRadiusLogDerivative (-L) - L) * L⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero] using ht
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp
  ring

theorem hasDerivAt_centralLogRadius (x : ℝ) :
    HasDerivAt (fun t : ℝ => log (centralRadius t)) (centralRadiusLogDerivative x) x := by
  simpa only [centralRadiusLogDerivative, deriv_centralRadius] using
    (hasDerivAt_centralRadius x).log (centralRadius_pos x).ne'

theorem range_centralLogRadius :
    range (fun x : ℝ => log (centralRadius x)) = univ := by
  apply eq_univ_of_forall
  intro y
  refine ⟨centralModelCoordinate (exp y), ?_⟩
  change log (centralRadius (centralModelCoordinate (exp y))) = y
  rw [centralRadius_modelCoordinate (exp_pos y), log_exp]

theorem hasDerivAt_centralLogRadiusInverse (y : ℝ) :
    HasDerivAt (fun t : ℝ => centralModelCoordinate (exp t))
      (centralRadiusLogDerivative (centralModelCoordinate (exp y)))⁻¹ y := by
  let x : ℝ := centralModelCoordinate (exp y)
  have hR : centralRadius x = exp y := centralRadius_modelCoordinate (exp_pos y)
  have hd := ((hasStrictDerivAt_centralModelCoordinate x).hasDerivAt).comp_of_eq y
    (hasDerivAt_exp y) hR
  change HasDerivAt (fun t : ℝ => centralModelCoordinate (exp t)) _ y at hd
  change HasDerivAt (fun t : ℝ => centralModelCoordinate (exp t))
    (centralRadiusLogDerivative x)⁻¹ y
  have hn : (centralRadiusLogDerivative x)⁻¹ = (deriv centralRadius x)⁻¹ * exp y := by
    unfold centralRadiusLogDerivative
    rw [inv_div, div_eq_mul_inv, hR, mul_comm]
  rw [hn]
  exact hd

/-- The actual radial height differentiated in logarithmic radial coordinate. -/
theorem centralKernelHeight_logarithmic_derivative (x : ℝ) :
    deriv (fun y : ℝ => centralKernelHeight (exp y)) (log (centralRadius x)) /
      centralKernelHeight (centralRadius x) =
      (centralRadiusA - 2 * x) / centralRadiusLogDerivative x := by
  have ht := (hasStrictDerivAt_centralModelCoordinate x).hasDerivAt
  have hh := ((ht.const_mul centralRadiusA).sub (ht.pow 2)).exp
  change HasDerivAt centralKernelHeight _ (centralRadius x) at hh
  have he : HasDerivAt exp (centralRadius x) (log (centralRadius x)) := by
    simpa only [exp_log (centralRadius_pos x)] using hasDerivAt_exp (log (centralRadius x))
  have heq := exp_log (centralRadius_pos x)
  have hh' : HasDerivAt centralKernelHeight
      (exp (centralRadiusA * centralModelCoordinate (centralRadius x) -
        centralModelCoordinate (centralRadius x) ^ 2) *
        (centralRadiusA * (deriv centralRadius x)⁻¹ -
          2 * centralModelCoordinate (centralRadius x) * (deriv centralRadius x)⁻¹))
      (exp (log (centralRadius x))) := by
    simpa only [heq, Pi.sub_apply, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat] using hh
  have hd := hh'.comp (log (centralRadius x)) he
  change HasDerivAt (fun y : ℝ => centralKernelHeight (exp y)) _ (log (centralRadius x)) at hd
  rw [hd.deriv, centralModelCoordinate_radius, centralKernelHeight_pullback]
  unfold centralRadiusLogDerivative
  field_simp [(exp_pos (centralRadiusA * x - x ^ 2)).ne',
    (centralRadius_pos x).ne', (deriv_centralRadius_pos x).ne']

theorem centralKernelHeight_left_logarithmic_slope_tendsto :
    Tendsto (fun L : ℝ =>
      deriv (fun y : ℝ => centralKernelHeight (exp y)) (log (centralRadius (-L))) /
        centralKernelHeight (centralRadius (-L))) atTop (𝓝 2) := by
  simp only [centralKernelHeight_logarithmic_derivative]
  have hnum : Tendsto (fun L : ℝ => centralRadiusA / L + 2) atTop (𝓝 2) := by
    simpa only [zero_add, pow_one] using
      (constant_div_pow_tendsto_zero centralRadiusA 1 (by decide)).add_const 2
  have ht := hnum.div centralRadiusLogDerivative_left_ratio_tendsto (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun L : ℝ => (centralRadiusA / L + 2) /
    (centralRadiusLogDerivative (-L) / L)) atTop (𝓝 (2 / 1 : ℝ)) at ht
  have hs : Tendsto (fun L : ℝ => (centralRadiusA / L + 2) /
      (centralRadiusLogDerivative (-L) / L)) atTop (𝓝 2) := by
    simpa only [div_one] using ht
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp
  ring

/-- The logarithmic derivative of the actual positive radial profile,
not a coefficient named after that derivative. -/
theorem centralRadialProfile_logarithmic_derivative {c : ℝ} (hc : 0 < c) (x : ℝ) :
    deriv (fun y : ℝ => log (centralRadialProfile c (exp y)))
      (log (centralRadius x)) =
      (x ^ 2 - centralOscillatorA) / centralRadiusLogDerivative x ^ 2 := by
  have hw := ((contDiffAt_centralRadialProfile c x).differentiableAt (by simp)).hasDerivAt
  have he : HasDerivAt exp (centralRadius x) (log (centralRadius x)) := by
    simpa only [exp_log (centralRadius_pos x)] using hasDerivAt_exp (log (centralRadius x))
  have heq := exp_log (centralRadius_pos x)
  have hcomp := hw.comp_of_eq (log (centralRadius x)) he heq.symm
  have hn : centralRadialProfile c (exp (log (centralRadius x))) ≠ 0 := by
    rw [heq]
    exact (centralRadialProfile_pos hc (centralRadius_pos x)).ne'
  have hd := hcomp.log hn
  change HasDerivAt (fun y : ℝ => log (centralRadialProfile c (exp y))) _ _ at hd
  rw [hd.deriv]
  dsimp only [Function.comp_apply]
  rw [heq]
  have hscaled := centralRadialProfile_deriv_scaled c x
  have hw' : deriv (centralRadialProfile c) (centralRadius x) =
      c * centralDensityRoot x ^ 2 * centralRadius x * (x ^ 2 - centralOscillatorA) /
        deriv centralRadius x :=
    (eq_div_iff (deriv_centralRadius_pos x).ne').mpr hscaled
  rw [hw', centralRadialProfile_pullback]
  unfold centralRadiusLogDerivative
  field_simp [hc.ne', (centralDensityRoot_pos x).ne',
    (centralRadius_pos x).ne', (deriv_centralRadius_pos x).ne']

theorem centralRadialProfile_left_logarithmic_slope_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun L : ℝ =>
      deriv (fun y : ℝ => log (centralRadialProfile c (exp y)))
        (log (centralRadius (-L)))) atTop (𝓝 1) := by
  simp only [centralRadialProfile_logarithmic_derivative hc, neg_sq]
  have hnum : Tendsto (fun L : ℝ => 1 - centralOscillatorA / L ^ 2) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (constant_div_pow_tendsto_zero centralOscillatorA 2 (by decide))
  have hden := centralRadiusLogDerivative_left_ratio_tendsto.pow 2
  have ht := hnum.div hden (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  change Tendsto (fun L : ℝ => (1 - centralOscillatorA / L ^ 2) /
      (centralRadiusLogDerivative (-L) / L) ^ 2) atTop (𝓝 (1 / 1 ^ 2 : ℝ)) at ht
  have hs : Tendsto (fun L : ℝ => (1 - centralOscillatorA / L ^ 2) /
      (centralRadiusLogDerivative (-L) / L) ^ 2) atTop (𝓝 1) := by simpa only [one_pow, div_one] using ht
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp

private theorem radialSymbolBounds_congr_positive {L0 s : ℝ} {f g : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (hfg : EqOn f g (Ioi 0)) :
    RadialSymbolBounds L0 s g := by
  refine ⟨hf.1.congr (fun L hL => (hfg hL).symm), ?_⟩
  intro r
  obtain ⟨C, hC, hCf⟩ := hf.2 r
  refine ⟨C, hC, ?_⟩
  intro L hL0 hL
  rw [← hfg.iteratedDeriv_of_isOpen isOpen_Ioi r hL]
  exact hCf L hL0 hL

def centralLeftLogDerivativeError (L : ℝ) : ℝ :=
  centralRadiusLogDerivative (-L) - (centralRadiusA + L + centralRadiusAlpha / L)

/-- The cubic left-end error holds after every actual derivative, on the
same explicit tail. Only the constants depend on the derivative order. -/
theorem centralRadiusLogDerivative_left_symbol :
    RadialSymbolBounds (centralRadiusAlpha + 1) (-3) centralLeftLogDerivativeError := by
  let β : ℝ := centralRadiusAlpha
  let L0 : ℝ := β + 1
  have hβ : 0 < β := by dsimp [β]; linarith [centralRadiusAlpha_gt_half]
  have hβ1 : 0 < β + 1 := by linarith
  have hE0 := gaussianLaplaceMoment_left_error_symbol hβ L0
  have hE1 : RadialSymbolBounds L0 (-β - 3)
      (fun L => gaussianLaplaceMoment (β + 1) (-L) -
        gammaLaplaceMoment (β + 1) (sqrt 2 * L)) := by
    simpa only [show -(β + 1) - 2 = -β - 3 by ring] using
      gaussianLaplaceMoment_left_error_symbol hβ1 L0
  have hq := gammaLaplaceQuotient_left_symbol β L0
  have hprod : RadialSymbolBounds L0 (-β - 3)
      ((fun L : ℝ => β / (sqrt 2 * L)) *
        (fun L => gaussianLaplaceMoment β (-L) - gammaLaplaceMoment β (sqrt 2 * L))) := by
    simpa only [show (-1 : ℝ) + (-β - 2) = -β - 3 by ring] using hq.mul hE0
  have hN : RadialSymbolBounds L0 (-β - 3)
      (fun L => gaussianLaplaceMoment (β + 1) (-L) -
        (β / (sqrt 2 * L)) * gaussianLaplaceMoment β (-L)) := by
    apply radialSymbolBounds_congr_positive (hE1.sub hprod)
    intro L hL
    change (gaussianLaplaceMoment (β + 1) (-L) - gammaLaplaceMoment (β + 1) (sqrt 2 * L)) -
      (β / (sqrt 2 * L)) *
        (gaussianLaplaceMoment β (-L) - gammaLaplaceMoment β (sqrt 2 * L)) = _
    rw [gammaLaplaceMoment_left_succ hβ hL]
    ring
  have hc : 0 < gammaLaplaceMoment β (sqrt 2) / 2 :=
    div_pos (gammaLaplaceMoment_pos hβ (sqrt_pos.mpr (by norm_num))) (by norm_num)
  have hquot := hN.div (gaussianLaplaceMoment_left_symbol hβ L0)
    (gaussianLaplaceMoment_left_ne_zero hβ) hc
    (fun L hL0 _ => gaussianLaplaceMoment_left_lower hβ hL0)
  have hquot' : RadialSymbolBounds L0 (-3)
      ((fun L => gaussianLaplaceMoment (β + 1) (-L) -
        (β / (sqrt 2 * L)) * gaussianLaplaceMoment β (-L)) /
        (fun L => gaussianLaplaceMoment β (-L))) := by
    simpa only [show (-β - 3) - (-β) = (-3 : ℝ) by ring] using hquot
  apply radialSymbolBounds_congr_positive (hquot'.const_mul (sqrt 2))
  intro L hL
  change sqrt 2 * ((gaussianLaplaceMoment (β + 1) (-L) -
    (β / (sqrt 2 * L)) * gaussianLaplaceMoment β (-L)) /
      gaussianLaplaceMoment β (-L)) = centralLeftLogDerivativeError L
  unfold centralLeftLogDerivativeError
  rw [centralRadiusLogDerivative_eq]
  change sqrt 2 * ((gaussianLaplaceMoment (β + 1) (-L) -
    (β / (sqrt 2 * L)) * gaussianLaplaceMoment β (-L)) /
      gaussianLaplaceMoment β (-L)) =
    centralRadiusA - -L + sqrt 2 * gaussianLaplaceRatio β (-L) -
      (centralRadiusA + L + β / L)
  unfold gaussianLaplaceRatio
  field_simp [(gaussianLaplaceMoment_pos hβ (-L)).ne',
    (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  all_goals ring

theorem centralRadiusLogDerivative_left_derivative_error (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, centralRadiusAlpha + 1 ≤ L →
      ‖iteratedDeriv r centralLeftLogDerivativeError L‖ ≤ C * L ^ (-3 - (r : ℝ)) := by
  obtain ⟨C, hC, hCL⟩ := centralRadiusLogDerivative_left_symbol.2 r
  refine ⟨C, hC, ?_⟩
  intro L hL
  exact hCL L hL (by linarith [centralRadiusAlpha_gt_half])

/-- The same all-order statement in the manuscript's original negative
`X` coordinate, with natural powers in the denominator. -/
theorem centralRadiusLogDerivative_left_original_derivative_error (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ≤ -(centralRadiusAlpha + 1) →
      |iteratedDeriv r (fun y : ℝ => centralRadiusLogDerivative y -
        (-y + centralRadiusA - centralRadiusAlpha / y)) x| ≤ C / |x| ^ (3 + r) := by
  obtain ⟨C, hC, hCr⟩ := centralRadiusLogDerivative_left_derivative_error r
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hxneg : x < 0 := by linarith [centralRadiusAlpha_gt_half]
  have hLp : 0 < -x := neg_pos.mpr hxneg
  have hL : centralRadiusAlpha + 1 ≤ -x := by linarith
  have heq : (fun y : ℝ => centralRadiusLogDerivative y -
      (-y + centralRadiusA - centralRadiusAlpha / y)) =
      (fun y => centralLeftLogDerivativeError (-y)) := by
    funext y
    simp only [centralLeftLogDerivativeError, neg_neg, div_neg]
    ring
  have hpow : (-x) ^ (-3 - (r : ℝ)) = 1 / |x| ^ (3 + r) := by
    rw [abs_of_neg hxneg,
      show (-3 : ℝ) - (r : ℝ) = -((3 + r : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hLp.le, Real.rpow_natCast, one_div]
  rw [← Real.norm_eq_abs, heq, iteratedDeriv_comp_neg, norm_smul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul]
  calc
    _ ≤ C * (-x) ^ (-3 - (r : ℝ)) := hCr (-x) hL
    _ = _ := by rw [hpow]; ring

private theorem left_rpow_symbol (L0 s : ℝ) :
    RadialSymbolBounds L0 s (fun L : ℝ => L ^ s) := by
  refine ⟨contDiffOn_id.rpow_const_of_ne (fun L hL => hL.ne'), ?_⟩
  intro r
  refine ⟨‖(descPochhammer ℝ r).eval s‖, norm_nonneg _, ?_⟩
  intro L _ hL
  rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, norm_mul,
    Real.norm_of_nonneg (rpow_nonneg hL.le _)]

private theorem left_symbol_order_mono {L0 s t : ℝ} {f : ℝ → ℝ}
    (hL0 : 1 ≤ L0) (hst : s ≤ t) (hf : RadialSymbolBounds L0 s f) :
    RadialSymbolBounds L0 t f := by
  refine ⟨hf.1, ?_⟩
  intro r
  obtain ⟨C, hC, hCf⟩ := hf.2 r
  refine ⟨C, hC, ?_⟩
  intro L hL hLp
  exact (hCf L hL hLp).trans (mul_le_mul_of_nonneg_left
    (rpow_le_rpow_of_exponent_le (hL0.trans hL) (sub_le_sub_right hst _)) hC)

private theorem left_constant_symbol (a L0 s : ℝ) (hL0 : 1 ≤ L0) (hs : 0 ≤ s) :
    RadialSymbolBounds L0 s (fun _ : ℝ => a) := by
  have hc := (left_rpow_symbol L0 0).const_mul a
  have hh := left_symbol_order_mono hL0 hs hc
  simpa only [rpow_zero, mul_one] using hh

theorem centralRadiusLogDerivative_left_growth_symbol :
    RadialSymbolBounds (centralRadiusAlpha + 1) 1
      (fun L : ℝ => centralRadiusLogDerivative (-L)) := by
  let L0 : ℝ := centralRadiusAlpha + 1
  have hL0 : 1 ≤ L0 := by dsimp [L0]; linarith [centralRadiusAlpha_gt_half]
  have hid := left_rpow_symbol L0 1
  have hc := left_constant_symbol centralRadiusA L0 1 hL0 (by norm_num)
  have hq := left_symbol_order_mono hL0 (by norm_num : (-1 : ℝ) ≤ 1)
    ((gammaLaplaceQuotient_left_symbol centralRadiusAlpha L0).const_mul (sqrt 2))
  have he := left_symbol_order_mono hL0 (by norm_num : (-3 : ℝ) ≤ 1)
    centralRadiusLogDerivative_left_symbol
  apply (((hid.add hc).add hq).add he).congr
  intro L hL
  change centralRadiusLogDerivative (-L) = L ^ (1 : ℝ) + centralRadiusA +
    sqrt 2 * (centralRadiusAlpha / (sqrt 2 * L)) + centralLeftLogDerivativeError L
  rw [rpow_one]
  unfold centralLeftLogDerivativeError
  field_simp [(sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  all_goals ring

theorem centralRadiusLogDerivative_left_lower (L : ℝ) :
    L ≤ centralRadiusLogDerivative (-L) := by
  have hβ : 0 < centralRadiusAlpha := by linarith [centralRadiusAlpha_gt_half]
  have hm := mul_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    (gaussianLaplaceRatio_pos hβ (-L))
  rw [centralRadiusLogDerivative_eq]
  linarith [centralRadiusA_pos]

theorem centralRadiusLogDerivative_left_inverse_symbol :
    RadialSymbolBounds (centralRadiusAlpha + 1) (-1)
      (fun L : ℝ => (centralRadiusLogDerivative (-L))⁻¹) := by
  apply centralRadiusLogDerivative_left_growth_symbol.inv
    (fun L => (centralRadiusLogDerivative_pos (-L)).ne') (c := 1) (by norm_num)
  intro L _ _
  simpa only [one_mul, rpow_one] using centralRadiusLogDerivative_left_lower L

/-- The actual height's logarithmic slope has bounded derivative symbols
on the same left tail, before the material-coordinate chain is applied. -/
theorem centralKernelHeight_left_slope_symbol :
    RadialSymbolBounds (centralRadiusAlpha + 1) 0
      (fun L : ℝ => (centralRadiusA + 2 * L) / centralRadiusLogDerivative (-L)) := by
  let L0 : ℝ := centralRadiusAlpha + 1
  have hL0 : 1 ≤ L0 := by dsimp [L0]; linarith [centralRadiusAlpha_gt_half]
  have hn := (left_constant_symbol centralRadiusA L0 1 hL0 (by norm_num)).add
    ((left_rpow_symbol L0 1).const_mul 2)
  have hh := hn.mul centralRadiusLogDerivative_left_inverse_symbol
  apply (show RadialSymbolBounds L0 0 _ from by
    simpa only [show (1 : ℝ) + -1 = 0 by norm_num] using hh).congr
  intro L _
  change (centralRadiusA + 2 * L) / centralRadiusLogDerivative (-L) =
    (centralRadiusA + 2 * L ^ (1 : ℝ)) * (centralRadiusLogDerivative (-L))⁻¹
  rw [rpow_one, div_eq_mul_inv]

theorem centralRadialProfile_left_slope_symbol :
    RadialSymbolBounds (centralRadiusAlpha + 1) 0
      (fun L : ℝ => (L ^ 2 - centralOscillatorA) / centralRadiusLogDerivative (-L) ^ 2) := by
  let L0 : ℝ := centralRadiusAlpha + 1
  have hL0 : 1 ≤ L0 := by dsimp [L0]; linarith [centralRadiusAlpha_gt_half]
  have hn := (left_rpow_symbol L0 2).add
    (left_constant_symbol (-centralOscillatorA) L0 2 hL0 (by norm_num))
  have hi := centralRadiusLogDerivative_left_inverse_symbol.mul
    centralRadiusLogDerivative_left_inverse_symbol
  have hh := hn.mul hi
  apply (show RadialSymbolBounds L0 0 _ from by
    simpa only [show (2 : ℝ) + (-1 + -1) = 0 by norm_num] using hh).congr
  intro L _
  change (L ^ 2 - centralOscillatorA) / centralRadiusLogDerivative (-L) ^ 2 =
    (L ^ (2 : ℝ) + -centralOscillatorA) *
      ((centralRadiusLogDerivative (-L))⁻¹ * (centralRadiusLogDerivative (-L))⁻¹)
  rw [rpow_two, div_eq_mul_inv, ← inv_pow]
  ring

end ContinuousFlexibility.Radial
