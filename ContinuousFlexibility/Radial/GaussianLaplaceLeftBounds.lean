import ContinuousFlexibility.Radial.GaussianLaplace
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Quantitative left-end bounds for the actual Laplace--Gaussian integral

Comparison with a genuine Gamma--Laplace integral gives a relative
O(L⁻²) error, for every positive moment parameter. The identities for
all iterated derivatives retain the shifted moment parameters explicitly.
This is a left-end input to R03.07, not the complete two-end expansion.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def gammaLaplaceKernel (β rate t : ℝ) : ℝ := t ^ (β - 1) * exp (-(rate * t))

def gammaLaplaceMoment (β rate : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), gammaLaplaceKernel β rate t

theorem gammaLaplaceMoment_eq {β rate : ℝ} (hβ : 0 < β) (hrate : 0 < rate) :
    gammaLaplaceMoment β rate = (1 / rate) ^ β * Gamma β :=
  integral_rpow_mul_exp_neg_mul_Ioi hβ hrate

theorem gammaLaplaceMoment_pos {β rate : ℝ} (hβ : 0 < β) (hrate : 0 < rate) :
    0 < gammaLaplaceMoment β rate := by
  rw [gammaLaplaceMoment_eq hβ hrate]
  exact mul_pos (rpow_pos_of_pos (one_div_pos.mpr hrate) _) (Gamma_pos_of_pos hβ)

theorem integrableOn_gammaLaplaceKernel {β rate : ℝ} (hβ : 0 < β) (hrate : 0 < rate) :
    IntegrableOn (gammaLaplaceKernel β rate) (Ioi 0) :=
  Integrable.of_integral_ne_zero (gammaLaplaceMoment_pos hβ hrate).ne'

theorem gammaLaplaceKernel_succ (β rate : ℝ) {t : ℝ} (ht : 0 < t) :
    gammaLaplaceKernel (β + 1) rate t = t * gammaLaplaceKernel β rate t := by
  have hr : t ^ β = t ^ (β - 1) * t := by
    calc
      _ = t ^ (β - 1 + 1) := by congr 1; ring
      _ = _ := rpow_add_one ht.ne' (β - 1)
  simp only [gammaLaplaceKernel, add_sub_cancel_right, hr]
  ring

theorem gammaLaplaceMoment_succ {β rate : ℝ} (hβ : 0 < β) (hrate : 0 < rate) :
    gammaLaplaceMoment (β + 1) rate = (β / rate) * gammaLaplaceMoment β rate := by
  rw [gammaLaplaceMoment_eq (by linarith : 0 < β + 1) hrate,
    gammaLaplaceMoment_eq hβ hrate, Gamma_add_one hβ.ne',
    rpow_add_one (one_div_ne_zero hrate.ne')]
  ring

theorem gammaLaplaceMoment_succ_two {β rate : ℝ} (hβ : 0 < β) (hrate : 0 < rate) :
    gammaLaplaceMoment (β + 1 + 1) rate =
      (β * (β + 1) / rate ^ 2) * gammaLaplaceMoment β rate := by
  rw [gammaLaplaceMoment_succ (by linarith : 0 < β + 1) hrate,
    gammaLaplaceMoment_succ hβ hrate]
  ring

theorem gaussianLaplaceKernel_left_factor (β L t : ℝ) :
    gaussianLaplaceKernel β (-L) t =
      gammaLaplaceKernel β (sqrt 2 * L) t * exp (-t ^ 2 / 2) := by
  unfold gaussianLaplaceKernel gammaLaplaceKernel
  rw [show -t ^ 2 / 2 + sqrt 2 * (-L) * t =
      -(sqrt 2 * L * t) + (-t ^ 2 / 2) by ring, exp_add]
  ring

private theorem gaussian_defect_bounds (t : ℝ) :
    0 ≤ 1 - exp (-t ^ 2 / 2) ∧ 1 - exp (-t ^ 2 / 2) ≤ t ^ 2 / 2 := by
  have hle : exp (-t ^ 2 / 2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have hge := add_one_le_exp (-t ^ 2 / 2)
  constructor <;> linarith

theorem gaussianLaplaceKernel_left_defect (β L : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ gammaLaplaceKernel β (sqrt 2 * L) t - gaussianLaplaceKernel β (-L) t ∧
      gammaLaplaceKernel β (sqrt 2 * L) t - gaussianLaplaceKernel β (-L) t ≤
        (1 / 2 : ℝ) * gammaLaplaceKernel (β + 1 + 1) (sqrt 2 * L) t := by
  rw [gaussianLaplaceKernel_left_factor]
  have hk : 0 ≤ gammaLaplaceKernel β (sqrt 2 * L) t := by
    unfold gammaLaplaceKernel
    exact (mul_pos (rpow_pos_of_pos ht _) (exp_pos _)).le
  have hd := gaussian_defect_bounds t
  have hfactor : gammaLaplaceKernel β (sqrt 2 * L) t -
      gammaLaplaceKernel β (sqrt 2 * L) t * exp (-t ^ 2 / 2) =
      gammaLaplaceKernel β (sqrt 2 * L) t * (1 - exp (-t ^ 2 / 2)) := by ring
  rw [hfactor]
  refine ⟨mul_nonneg hk hd.1, ?_⟩
  calc
    _ ≤ gammaLaplaceKernel β (sqrt 2 * L) t * (t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hd.2 hk
    _ = _ := by
      simp only [gammaLaplaceKernel_succ (β + 1) _ ht, gammaLaplaceKernel_succ β _ ht]
      ring

/-- The integral error is bounded by an actual higher Gamma moment. -/
theorem gaussianLaplaceMoment_left_defect {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) :
    0 ≤ gammaLaplaceMoment β (sqrt 2 * L) - gaussianLaplaceMoment β (-L) ∧
      gammaLaplaceMoment β (sqrt 2 * L) - gaussianLaplaceMoment β (-L) ≤
        (1 / 2 : ℝ) * gammaLaplaceMoment (β + 1 + 1) (sqrt 2 * L) := by
  have hrate : 0 < sqrt 2 * L := by positivity
  have hJ := integrableOn_gammaLaplaceKernel hβ hrate
  have hM := integrableOn_gaussianLaplaceKernel hβ (-L)
  have hJ2 := integrableOn_gammaLaplaceKernel (by linarith : 0 < β + 1 + 1) hrate
  have hdiff : IntegrableOn (fun t => gammaLaplaceKernel β (sqrt 2 * L) t -
      gaussianLaplaceKernel β (-L) t) (Ioi 0) := hJ.sub hM
  have hbound : IntegrableOn (fun t =>
      (1 / 2 : ℝ) * gammaLaplaceKernel (β + 1 + 1) (sqrt 2 * L) t) (Ioi 0) := hJ2.const_mul _
  have hn : 0 ≤ ∫ t in Ioi (0 : ℝ), gammaLaplaceKernel β (sqrt 2 * L) t -
      gaussianLaplaceKernel β (-L) t := by
    apply integral_nonneg_of_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => (gaussianLaplaceKernel_left_defect β L ht).1)
  have hb := integral_mono_ae hdiff hbound (ae_restrict_of_forall_mem measurableSet_Ioi
    (fun t ht => (gaussianLaplaceKernel_left_defect β L ht).2))
  rw [integral_sub hJ hM] at hn hb
  rw [integral_const_mul] at hb
  exact ⟨hn, hb⟩

/-- A fully quantitative relative left-end error for every positive
moment parameter, without postulating a Laplace asymptotic formula. -/
theorem gaussianLaplaceMoment_left_relative_error {β L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) :
    0 ≤ 1 - gaussianLaplaceMoment β (-L) / gammaLaplaceMoment β (sqrt 2 * L) ∧
      1 - gaussianLaplaceMoment β (-L) / gammaLaplaceMoment β (sqrt 2 * L) ≤
        β * (β + 1) / (4 * L ^ 2) := by
  have hrate : 0 < sqrt 2 * L := by positivity
  have hp := gammaLaplaceMoment_pos hβ hrate
  have hd := gaussianLaplaceMoment_left_defect hβ hL
  have hid : 1 - gaussianLaplaceMoment β (-L) / gammaLaplaceMoment β (sqrt 2 * L) =
      (gammaLaplaceMoment β (sqrt 2 * L) - gaussianLaplaceMoment β (-L)) /
        gammaLaplaceMoment β (sqrt 2 * L) := by rw [sub_div, div_self hp.ne']
  rw [hid]
  refine ⟨div_nonneg hd.1 hp.le, (div_le_iff₀ hp).mpr ?_⟩
  calc
    _ ≤ (1 / 2 : ℝ) * gammaLaplaceMoment (β + 1 + 1) (sqrt 2 * L) := hd.2
    _ = _ := by
      rw [gammaLaplaceMoment_succ_two hβ hrate, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- All parameter derivatives are the actual shifted integral moments. -/
theorem iteratedDeriv_gaussianLaplaceMoment {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    iteratedDeriv k (gaussianLaplaceMoment β) =
      fun x => sqrt 2 ^ k * gaussianLaplaceMoment (β + (k : ℝ)) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hk : 0 < β + (k : ℝ) := by positivity
    have hh := (hasDerivAt_gaussianLaplaceMoment hk x).const_mul (sqrt 2 ^ k)
    have hindex : β + (k : ℝ) + 1 = β + ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hh.deriv, hindex, pow_succ]
    ring

theorem iteratedDeriv_gaussianLaplaceMoment_neg {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    iteratedDeriv k (fun x => gaussianLaplaceMoment β (-x)) =
      fun x => (-sqrt 2) ^ k * gaussianLaplaceMoment (β + (k : ℝ)) (-x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hk : 0 < β + (k : ℝ) := by positivity
    have hd := (hasDerivAt_gaussianLaplaceMoment hk (-x)).comp x (hasDerivAt_id x).neg
    have hh := hd.const_mul ((-sqrt 2) ^ k)
    change HasDerivAt (fun y => (-sqrt 2) ^ k * gaussianLaplaceMoment (β + (k : ℝ)) (-y)) _ x at hh
    have hindex : β + (k : ℝ) + 1 = β + ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hh.deriv, hindex, pow_succ]
    ring

/-- The same actual integral comparison controls every fixed derivative
order; no derivative estimate is inferred from a scalar big-O statement. -/
theorem gaussianLaplaceMoment_left_derivative_error {β L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (k : ℕ) :
    ‖iteratedDeriv k (fun x => gaussianLaplaceMoment β (-x)) L -
      (-sqrt 2) ^ k * gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * L)‖ ≤
      sqrt 2 ^ k * ((1 / 2 : ℝ) *
        gammaLaplaceMoment (β + (k : ℝ) + 1 + 1) (sqrt 2 * L)) := by
  have hk : 0 < β + (k : ℝ) := by positivity
  have hd := gaussianLaplaceMoment_left_defect hk hL
  rw [iteratedDeriv_gaussianLaplaceMoment_neg hβ k]
  calc
    _ = sqrt 2 ^ k * (gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * L) -
        gaussianLaplaceMoment (β + (k : ℝ)) (-L)) := by
      rw [show (-sqrt 2) ^ k * gaussianLaplaceMoment (β + (k : ℝ)) (-L) -
        (-sqrt 2) ^ k * gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * L) =
        (-sqrt 2) ^ k * (gaussianLaplaceMoment (β + (k : ℝ)) (-L) -
          gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * L)) by ring]
      rw [norm_mul, norm_pow, norm_neg, Real.norm_eq_abs,
        abs_of_nonneg (sqrt_nonneg 2), Real.norm_eq_abs,
        abs_of_nonpos (by linarith [hd.1])]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd.2 (pow_nonneg (sqrt_nonneg 2) _)

theorem gaussianLaplaceMoment_left_ratio_tendsto {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun L : ℝ => gaussianLaplaceMoment β (-L) /
      gammaLaplaceMoment β (sqrt 2 * L)) atTop (𝓝 1) := by
  have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hbound : Tendsto (fun L : ℝ => β * (β + 1) / (4 * L ^ 2)) atTop (𝓝 0) := by
    have heq : (fun L : ℝ => β * (β + 1) / (4 * L ^ 2)) =
        (fun L : ℝ => (β * (β + 1) / 4) * (L⁻¹) ^ 2) := by
      funext L
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    rw [heq]
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (hi.pow 2).const_mul (β * (β + 1) / 4)
  have he : Tendsto (fun L : ℝ => 1 - gaussianLaplaceMoment β (-L) /
      gammaLaplaceMoment β (sqrt 2 * L)) atTop (𝓝 0) :=
    squeeze_zero'
      ((eventually_gt_atTop (0 : ℝ)).mono
        (fun L hL => (gaussianLaplaceMoment_left_relative_error hβ hL).1))
      ((eventually_gt_atTop (0 : ℝ)).mono
        (fun L hL => (gaussianLaplaceMoment_left_relative_error hβ hL).2)) hbound
  have ht : Tendsto (fun L : ℝ => 1 - (1 - gaussianLaplaceMoment β (-L) /
      gammaLaplaceMoment β (sqrt 2 * L))) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub he
  simpa only [sub_sub_cancel, sub_zero] using ht

/-- A leading Gamma asymptotic for each fixed actual derivative, with
the sign and the shifted moment preserved. -/
theorem gaussianLaplaceMoment_left_derivative_ratio_tendsto {β : ℝ}
    (hβ : 0 < β) (k : ℕ) :
    Tendsto (fun L : ℝ => iteratedDeriv k (fun x => gaussianLaplaceMoment β (-x)) L /
      ((-sqrt 2) ^ k * gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * L))) atTop (𝓝 1) := by
  have hk : 0 < β + (k : ℝ) := by positivity
  have hc : (-sqrt (2 : ℝ)) ^ k ≠ 0 :=
    pow_ne_zero k (neg_ne_zero.mpr (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')
  have heq : (fun L : ℝ => iteratedDeriv k (fun x => gaussianLaplaceMoment β (-x)) L /
      ((-sqrt 2) ^ k * gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * L))) =
      (fun L : ℝ => gaussianLaplaceMoment (β + (k : ℝ)) (-L) /
        gammaLaplaceMoment (β + (k : ℝ)) (sqrt 2 * L)) := by
    funext L
    rw [iteratedDeriv_gaussianLaplaceMoment_neg hβ k]
    exact mul_div_mul_left _ _ hc
  rw [heq]
  exact gaussianLaplaceMoment_left_ratio_tendsto hk

end ContinuousFlexibility.Radial
