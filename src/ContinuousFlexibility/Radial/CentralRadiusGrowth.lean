module

public import ContinuousFlexibility.Radial.CentralRadius

/-!
# Global growth of the actual central logarithmic radius derivative

The moment variance is an integral of a nonnegative square against the
actual half-line Gaussian kernel. It bounds the logarithmic derivative
of the already constructed radius. Full differentiated end expansions
are separate obligations of R03.07.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem gaussianLaplaceMoment_variance {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    gaussianLaplaceMoment (β + 1) x ^ 2 ≤
      gaussianLaplaceMoment β x * gaussianLaplaceMoment (β + 1 + 1) x := by
  let M0 := gaussianLaplaceMoment β x
  let M1 := gaussianLaplaceMoment (β + 1) x
  have h0 := integrableOn_gaussianLaplaceKernel hβ x
  have h1 := integrableOn_gaussianLaplaceKernel (by linarith : 0 < β + 1) x
  have h2 := integrableOn_gaussianLaplaceKernel (by linarith : 0 < β + 1 + 1) x
  have hpos : 0 < M0 := gaussianLaplaceMoment_pos hβ x
  have hn : 0 ≤ ∫ t in Ioi (0 : ℝ),
      M0 ^ 2 * gaussianLaplaceKernel (β + 1 + 1) x t -
        (2 * M0 * M1) * gaussianLaplaceKernel (β + 1) x t +
        M1 ^ 2 * gaussianLaplaceKernel β x t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [gaussianLaplaceKernel_succ (β + 1) x ht,
      gaussianLaplaceKernel_succ β x ht]
    convert mul_nonneg (sq_nonneg (M0 * t - M1))
      (gaussianLaplaceKernel_pos β x ht).le using 1
    ring
  rw [integral_add
      (f := fun t => M0 ^ 2 * gaussianLaplaceKernel (β + 1 + 1) x t -
        (2 * M0 * M1) * gaussianLaplaceKernel (β + 1) x t)
      (g := fun t => M1 ^ 2 * gaussianLaplaceKernel β x t)
      ((h2.const_mul (M0 ^ 2)).sub (h1.const_mul (2 * M0 * M1)))
      (h0.const_mul (M1 ^ 2)),
    integral_sub
      (f := fun t => M0 ^ 2 * gaussianLaplaceKernel (β + 1 + 1) x t)
      (g := fun t => (2 * M0 * M1) * gaussianLaplaceKernel (β + 1) x t)
      (h2.const_mul (M0 ^ 2)) (h1.const_mul (2 * M0 * M1)),
    integral_const_mul, integral_const_mul, integral_const_mul] at hn
  change 0 ≤ M0 ^ 2 * gaussianLaplaceMoment (β + 1 + 1) x -
    (2 * M0 * M1) * M1 + M1 ^ 2 * M0 at hn
  have hmul : 0 ≤ M0 * (M0 * gaussianLaplaceMoment (β + 1 + 1) x - M1 ^ 2) := by
    nlinarith only [hn]
  have hv := (mul_nonneg_iff_of_pos_left hpos).mp hmul
  dsimp [M0, M1] at hv
  linarith

def gaussianLaplaceRatio (β x : ℝ) : ℝ :=
  gaussianLaplaceMoment (β + 1) x / gaussianLaplaceMoment β x

theorem gaussianLaplaceRatio_pos {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    0 < gaussianLaplaceRatio β x :=
  div_pos (gaussianLaplaceMoment_pos (by linarith : 0 < β + 1) x)
    (gaussianLaplaceMoment_pos hβ x)

theorem gaussianLaplaceRatio_quadratic {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    gaussianLaplaceRatio β x ^ 2 ≤ sqrt 2 * x * gaussianLaplaceRatio β x + β := by
  have hm := gaussianLaplaceMoment_pos hβ x
  calc
    _ = gaussianLaplaceMoment (β + 1) x ^ 2 / gaussianLaplaceMoment β x ^ 2 := div_pow _ _ _
    _ ≤ (gaussianLaplaceMoment β x * gaussianLaplaceMoment (β + 1 + 1) x) /
        gaussianLaplaceMoment β x ^ 2 :=
      div_le_div_of_nonneg_right (gaussianLaplaceMoment_variance hβ x) (sq_nonneg _)
    _ = _ := by
      rw [gaussianLaplaceMoment_recurrence hβ]
      unfold gaussianLaplaceRatio
      field_simp [hm.ne']
      ring

theorem gaussianLaplaceRatio_le_sqrt_of_nonpos {β x : ℝ}
    (hβ : 0 < β) (hx : x ≤ 0) : gaussianLaplaceRatio β x ≤ sqrt β := by
  have hm := gaussianLaplaceRatio_pos hβ x
  have hquad := gaussianLaplaceRatio_quadratic hβ x
  have hcross : sqrt 2 * x * gaussianLaplaceRatio β x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sqrt_nonneg 2) hx) hm.le
  have hs := sq_sqrt hβ.le
  nlinarith [sqrt_nonneg β]

theorem gaussianLaplaceRatio_le_of_nonneg {β x : ℝ}
    (hβ : 0 < β) (hx : 0 ≤ x) : gaussianLaplaceRatio β x ≤ sqrt 2 * x + sqrt β := by
  have hm := gaussianLaplaceRatio_pos hβ x
  have hquad := gaussianLaplaceRatio_quadratic hβ x
  by_contra h
  have hlt : sqrt 2 * x + sqrt β < gaussianLaplaceRatio β x := lt_of_not_ge h
  have hqx : 0 ≤ sqrt 2 * x := mul_nonneg (sqrt_nonneg 2) hx
  have hmt : sqrt β < gaussianLaplaceRatio β x := by linarith
  have hmul := mul_lt_mul_of_pos_right hlt hm
  have htm := mul_lt_mul_of_pos_left hmt (sqrt_pos.mpr hβ)
  have hs := sq_sqrt hβ.le
  nlinarith only [hquad, hmul, htm, hs]

theorem gaussianLaplacePsi_log_deriv {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    deriv (gaussianLaplacePsi β) x / gaussianLaplacePsi β x =
      -x + sqrt 2 * gaussianLaplaceRatio β x := by
  rw [deriv_gaussianLaplacePsi hβ]
  unfold gaussianLaplacePsi gaussianLaplaceRatio
  field_simp [(exp_pos (-x ^ 2 / 2)).ne', (gaussianLaplaceMoment_pos hβ x).ne']
  ring

def centralRadiusLogDerivative (x : ℝ) : ℝ := deriv centralRadius x / centralRadius x

theorem centralRadiusLogDerivative_eq (x : ℝ) :
    centralRadiusLogDerivative x = centralRadiusA - x +
      sqrt 2 * gaussianLaplaceRatio centralRadiusAlpha x := by
  have hβ : 0 < centralRadiusAlpha := by linarith [centralRadiusAlpha_gt_half]
  have hfirst : centralRadiusLogDerivative x =
      centralRadiusA + deriv centralRadiusPsi x / centralRadiusPsi x := by
    unfold centralRadiusLogDerivative
    rw [deriv_centralRadius, centralRadius]
    field_simp [(exp_pos (centralRadiusA * x)).ne', (centralRadiusPsi_pos x).ne']
  rw [hfirst]
  change centralRadiusA + deriv (gaussianLaplacePsi centralRadiusAlpha) x /
    gaussianLaplacePsi centralRadiusAlpha x = _
  rw [gaussianLaplacePsi_log_deriv hβ]
  ring

theorem centralRadiusLogDerivative_gt (x : ℝ) :
    centralRadiusA < centralRadiusLogDerivative x := by
  unfold centralRadiusLogDerivative
  apply (lt_div_iff₀ (centralRadius_pos x)).mpr
  exact deriv_centralRadius_gt x

/-- A genuine global upper bound for the actual material weight. This
does not assert any differentiated endpoint asymptotic expansion. -/
theorem centralRadiusLogDerivative_le (x : ℝ) :
    centralRadiusLogDerivative x ≤
      centralRadiusA + |x| + sqrt (2 * centralRadiusAlpha) := by
  have hβ : 0 < centralRadiusAlpha := by linarith [centralRadiusAlpha_gt_half]
  have hconst : sqrt 2 * sqrt centralRadiusAlpha = sqrt (2 * centralRadiusAlpha) :=
    (sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) centralRadiusAlpha).symm
  rw [centralRadiusLogDerivative_eq]
  rcases le_total x 0 with hx | hx
  · have hh := mul_le_mul_of_nonneg_left (gaussianLaplaceRatio_le_sqrt_of_nonpos hβ hx)
      (sqrt_nonneg (2 : ℝ))
    rw [hconst] at hh
    rw [abs_of_nonpos hx]
    linarith
  · have hh := mul_le_mul_of_nonneg_left (gaussianLaplaceRatio_le_of_nonneg hβ hx)
      (sqrt_nonneg (2 : ℝ))
    have hscale : sqrt 2 * (sqrt 2 * x + sqrt centralRadiusAlpha) =
        2 * x + sqrt (2 * centralRadiusAlpha) := by
      calc
        _ = sqrt 2 ^ 2 * x + sqrt 2 * sqrt centralRadiusAlpha := by ring
        _ = _ := by rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hconst]
    rw [hscale] at hh
    rw [abs_of_nonneg hx]
    linarith

theorem centralRadiusLogDerivative_pos (x : ℝ) : 0 < centralRadiusLogDerivative x :=
  lt_trans centralRadiusA_pos (centralRadiusLogDerivative_gt x)

theorem contDiff_centralRadiusLogDerivative : ContDiff ℝ ∞ centralRadiusLogDerivative := by
  unfold centralRadiusLogDerivative
  exact ((contDiff_infty_iff_deriv.mp contDiff_centralRadius).2).div contDiff_centralRadius
    (fun x => (centralRadius_pos x).ne')

theorem centralRadiusLogDerivative_norm_le (x : ℝ) :
    ‖centralRadiusLogDerivative x‖ ≤
      centralRadiusA + |x| + sqrt (2 * centralRadiusAlpha) := by
  rw [Real.norm_eq_abs, abs_of_pos (centralRadiusLogDerivative_pos x)]
  exact centralRadiusLogDerivative_le x

def centralRadiusWeightConstant : ℝ :=
  centralRadiusA + sqrt (2 * centralRadiusAlpha) + 1

theorem centralRadiusWeightConstant_pos : 0 < centralRadiusWeightConstant := by
  unfold centralRadiusWeightConstant
  linarith [centralRadiusA_pos, sqrt_nonneg (2 * centralRadiusAlpha)]

theorem centralRadiusLogDerivative_norm_le_linear (x : ℝ) :
    ‖centralRadiusLogDerivative x‖ ≤ centralRadiusWeightConstant * (1 + |x|) := by
  have hh := centralRadiusLogDerivative_norm_le x
  have hp := mul_nonneg
    (add_nonneg centralRadiusA_pos.le (sqrt_nonneg (2 * centralRadiusAlpha))) (abs_nonneg x)
  unfold centralRadiusWeightConstant
  nlinarith

end ContinuousFlexibility.Radial
