module

public import ContinuousFlexibility.Analysis.MaterialWeights
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The actual left-endpoint material coordinate

For `d₀ > 0` and `0 < d < d₀`, the physical distance variable has material
coordinate `X(d) = sqrt(log(d₀/d))` and scale `ell(d) = d/(1+X(d))`.
All derivatives below are actual mathlib derivatives. The explicit
primitive `rho(X) = -X² - 2X³/3` has derivative `1/ell` in the distance
variable and tends to `-∞` at the left endpoint.

This is an endpoint model. No smooth middle interpolation or whole-line
material coordinate for the manuscript's actual discrete profile is
constructed here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def endpointX (d₀ d : ℝ) : ℝ := Real.sqrt (Real.log (d₀ / d))

def endpointEll (d₀ d : ℝ) : ℝ := d / (1 + endpointX d₀ d)

def endpointMaterialDerivative (d₀ : ℝ) (f : ℝ → ℝ) (d : ℝ) : ℝ :=
  endpointEll d₀ d * deriv f d

def endpointRho (x : ℝ) : ℝ := -x ^ 2 - (2 / 3 : ℝ) * x ^ 3

def endpointRhoOfDistance (d₀ d : ℝ) : ℝ := endpointRho (endpointX d₀ d)

def endpointDistance (d₀ x : ℝ) : ℝ := d₀ * Real.exp (-x ^ 2)

theorem endpoint_log_pos {d₀ d : ℝ} (hd : 0 < d) (hdd : d < d₀) :
    0 < Real.log (d₀ / d) :=
  Real.log_pos ((one_lt_div hd).mpr hdd)

theorem endpointX_pos {d₀ d : ℝ} (hd : 0 < d) (hdd : d < d₀) :
    0 < endpointX d₀ d := Real.sqrt_pos.mpr (endpoint_log_pos hd hdd)

theorem endpointEll_pos {d₀ d : ℝ} (hd : 0 < d) : 0 < endpointEll d₀ d := by
  apply div_pos hd
  have hx : 0 ≤ endpointX d₀ d := Real.sqrt_nonneg _
  linarith

theorem hasDerivAt_endpoint_log {d₀ d : ℝ} (hd₀ : 0 < d₀) (hd : 0 < d) :
    HasDerivAt (fun t : ℝ => Real.log (d₀ / t)) (-1 / d) d := by
  have hdiv : HasDerivAt (fun t : ℝ => d₀ / t) (-d₀ / d ^ 2) d := by
    convert (hasDerivAt_const d d₀).div (hasDerivAt_id d) hd.ne' using 1
    · ext t
      rfl
    · simp [id_eq]
  have hlog := hdiv.log (div_ne_zero hd₀.ne' hd.ne')
  apply hlog.congr_deriv
  field_simp [hd₀.ne', hd.ne']

theorem hasDerivAt_endpointX {d₀ d : ℝ} (hd₀ : 0 < d₀) (hd : 0 < d) (hdd : d < d₀) :
    HasDerivAt (endpointX d₀) (-1 / (2 * endpointX d₀ d * d)) d := by
  have hs := (hasDerivAt_endpoint_log hd₀ hd).sqrt (endpoint_log_pos hd hdd).ne'
  apply hs.congr_deriv
  unfold endpointX
  field_simp [hd.ne', (Real.sqrt_pos.mpr (endpoint_log_pos hd hdd)).ne']

theorem contDiffAt_endpointX {d₀ d : ℝ} (hd₀ : 0 < d₀) (hd : 0 < d) (hdd : d < d₀) :
    ContDiffAt ℝ ∞ (endpointX d₀) d := by
  have hdiv : ContDiffAt ℝ ∞ (fun t : ℝ => d₀ / t) d :=
    contDiffAt_const.div contDiffAt_id hd.ne'
  exact (hdiv.log (div_ne_zero hd₀.ne' hd.ne')).sqrt (endpoint_log_pos hd hdd).ne'

theorem endpointMaterialDerivative_X {d₀ d : ℝ}
    (hd₀ : 0 < d₀) (hd : 0 < d) (hdd : d < d₀) :
    endpointMaterialDerivative d₀ (endpointX d₀) d =
      -1 / (2 * endpointX d₀ d * (1 + endpointX d₀ d)) := by
  unfold endpointMaterialDerivative endpointEll
  rw [(hasDerivAt_endpointX hd₀ hd hdd).deriv]
  have hx := endpointX_pos hd hdd
  field_simp [hd.ne', hx.ne', (by linarith : 1 + endpointX d₀ d ≠ 0)]

theorem hasDerivAt_log_materialH_endpointX {d₀ d : ℝ}
    (hd₀ : 0 < d₀) (hd : 0 < d) (hdd : d < d₀) :
    HasDerivAt (fun t : ℝ => Real.log (materialH (endpointX d₀ t))) (endpointX d₀ d / d) d := by
  have hx := hasDerivAt_endpointX hd₀ hd hdd
  have hh := ((hx.pow 3).const_mul (-2 : ℝ)).div_const 3
  have heq : (fun t : ℝ => Real.log (materialH (endpointX d₀ t))) =
      (fun t => -2 * endpointX d₀ t ^ 3 / 3) := by
    funext t
    simp [materialH]
  rw [heq]
  convert hh using 1
  have hxp := endpointX_pos hd hdd
  field_simp [hd.ne', hxp.ne']
  ring

theorem endpointMaterialDerivative_logH {d₀ d : ℝ}
    (hd₀ : 0 < d₀) (hd : 0 < d) (hdd : d < d₀) :
    endpointMaterialDerivative d₀ (fun t => Real.log (materialH (endpointX d₀ t))) d =
      endpointX d₀ d / (1 + endpointX d₀ d) := by
  unfold endpointMaterialDerivative endpointEll
  rw [(hasDerivAt_log_materialH_endpointX hd₀ hd hdd).deriv]
  field_simp [hd.ne']

theorem endpointMaterialDerivative_logH_bounds {d₀ d : ℝ}
    (hd₀ : 0 < d₀) (hd : 0 < d) (hdd : d < d₀) :
    0 < endpointMaterialDerivative d₀ (fun t => Real.log (materialH (endpointX d₀ t))) d ∧
      endpointMaterialDerivative d₀ (fun t => Real.log (materialH (endpointX d₀ t))) d < 1 := by
  rw [endpointMaterialDerivative_logH hd₀ hd hdd]
  have hx := endpointX_pos hd hdd
  have hden : 0 < 1 + endpointX d₀ d := by linarith
  exact ⟨div_pos hx hden, (div_lt_one hden).mpr (by linarith)⟩

theorem hasDerivAt_endpointRho (x : ℝ) :
    HasDerivAt endpointRho (-2 * x * (1 + x)) x := by
  have h := ((hasDerivAt_id x).pow 2).neg.sub
    (((hasDerivAt_id x).pow 3).const_mul (2 / 3 : ℝ))
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

theorem hasDerivAt_endpointRhoOfDistance {d₀ d : ℝ}
    (hd₀ : 0 < d₀) (hd : 0 < d) (hdd : d < d₀) :
    HasDerivAt (endpointRhoOfDistance d₀) (1 / endpointEll d₀ d) d := by
  have h := (hasDerivAt_endpointRho (endpointX d₀ d)).comp d
    (hasDerivAt_endpointX hd₀ hd hdd)
  apply h.congr_deriv
  have hx := endpointX_pos hd hdd
  unfold endpointEll
  field_simp [hd.ne', hx.ne', (by linarith : 1 + endpointX d₀ d ≠ 0)]

theorem tendsto_endpointX_atTop {d₀ : ℝ} (hd₀ : 0 < d₀) :
    Tendsto (endpointX d₀) (𝓝[>] (0 : ℝ)) atTop := by
  have hdiv : Tendsto (fun d : ℝ => d₀ / d) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero : Tendsto (fun d : ℝ => d⁻¹) (𝓝[>] (0 : ℝ)) atTop).const_mul_atTop hd₀
  exact Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp hdiv)

theorem tendsto_endpointRho_atBot : Tendsto endpointRho atTop atBot := by
  have hp : Tendsto (fun x : ℝ => x ^ (3 : ℕ)) atTop atTop := tendsto_pow_atTop (by decide)
  have hn := hp.const_mul_atTop_of_neg (by norm_num : (-2 / 3 : ℝ) < 0)
  apply tendsto_atBot.2
  intro B
  filter_upwards [hn.eventually_le_atBot B] with x hx
  unfold endpointRho
  nlinarith [sq_nonneg x]

theorem tendsto_endpointRhoOfDistance_atBot {d₀ : ℝ} (hd₀ : 0 < d₀) :
    Tendsto (endpointRhoOfDistance d₀) (𝓝[>] (0 : ℝ)) atBot :=
  tendsto_endpointRho_atBot.comp (tendsto_endpointX_atTop hd₀)

theorem endpointDistance_pos {d₀ : ℝ} (hd₀ : 0 < d₀) (x : ℝ) :
    0 < endpointDistance d₀ x := mul_pos hd₀ (Real.exp_pos _)

theorem endpointX_endpointDistance {d₀ x : ℝ} (hd₀ : 0 < d₀) (hx : 0 ≤ x) :
    endpointX d₀ (endpointDistance d₀ x) = x := by
  have he : d₀ / endpointDistance d₀ x = Real.exp (x ^ 2) := by
    apply (div_eq_iff_mul_eq (endpointDistance_pos hd₀ x).ne').mpr
    unfold endpointDistance
    calc
      _ = d₀ * (Real.exp (x ^ 2) * Real.exp (-x ^ 2)) := by ring
      _ = d₀ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  unfold endpointX
  rw [he, Real.log_exp, Real.sqrt_sq_eq_abs, abs_of_nonneg hx]

theorem endpointDistance_endpointX {d₀ d : ℝ}
    (hd₀ : 0 < d₀) (hd : 0 < d) (hdd : d < d₀) :
    endpointDistance d₀ (endpointX d₀ d) = d := by
  have hs : endpointX d₀ d ^ 2 = Real.log (d₀ / d) :=
    Real.sq_sqrt (endpoint_log_pos hd hdd).le
  unfold endpointDistance
  rw [hs, Real.exp_neg, Real.exp_log (div_pos hd₀ hd)]
  field_simp [hd₀.ne', hd.ne']

theorem hasDerivAt_endpointDistance (d₀ x : ℝ) :
    HasDerivAt (endpointDistance d₀) (-2 * x * endpointDistance d₀ x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.exp).const_mul d₀
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  unfold endpointDistance
  ring

theorem endpointDistance_lt {d₀ x : ℝ} (hd₀ : 0 < d₀) (hx : 0 < x) :
    endpointDistance d₀ x < d₀ := by
  have he : Real.exp (-x ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (pow_pos hx 2))
  exact (mul_lt_mul_of_pos_left he hd₀).trans_eq (mul_one d₀)

theorem endpointMaterialDerivative_rho {d₀ d : ℝ}
    (hd₀ : 0 < d₀) (hd : 0 < d) (hdd : d < d₀) :
    endpointMaterialDerivative d₀ (endpointRhoOfDistance d₀) d = 1 := by
  unfold endpointMaterialDerivative
  rw [(hasDerivAt_endpointRhoOfDistance hd₀ hd hdd).deriv]
  field_simp [(endpointEll_pos hd).ne']

/-- The already-proved material envelope vanishes along the actual
physical endpoint distance, not merely along an abstract material tail. -/
theorem tendsto_endpoint_H_rpow_M_rpow_zero {d₀ : ℝ} (hd₀ : 0 < d₀)
    (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun d : ℝ => materialH (endpointX d₀ d) ^ ε * materialM (endpointX d₀ d) ^ A)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (tendsto_materialH_rpow_mul_materialM_rpow_zero A hε).comp (tendsto_endpointX_atTop hd₀)

theorem tendsto_endpoint_H_rpow_E0_rpow_zero {d₀ : ℝ} (hd₀ : 0 < d₀)
    (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun d : ℝ => materialH (endpointX d₀ d) ^ ε * materialE0 (endpointX d₀ d) ^ A)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (tendsto_materialH_rpow_mul_materialE0_rpow_zero A hε).comp (tendsto_endpointX_atTop hd₀)

end ContinuousFlexibility.Analysis
