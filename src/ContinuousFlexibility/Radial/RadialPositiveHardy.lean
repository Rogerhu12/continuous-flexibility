import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# A radial Hardy estimate for every nondecreasing positive gap

Completing a square retains the actual endpoint terms. Thus the
Dirichlet coercivity constant does not require a lower bound on the
logarithmic slope. Nonzero Poisson traces retain their explicit cost.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff

theorem radialPositiveHardy_boundary {a b J : ℝ} {w dw u du : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 < a)
    (hwc : ContinuousOn w (Icc a b)) (hdwc : ContinuousOn dw (Icc a b))
    (huc : ContinuousOn u (Icc a b)) (hduc : ContinuousOn du (Icc a b))
    (hw : ∀ r ∈ Ioo a b, HasDerivAt w (dw r) r)
    (hu : ∀ r ∈ Ioo a b, HasDerivAt u (du r) r)
    (hwn : ∀ r ∈ Icc a b, 0 ≤ w r)
    (hdwn : ∀ r ∈ Icc a b, 0 ≤ dw r) (hJ : 1 / 2 ≤ J) :
    (∫ r in a..b, (12 * w r / r ^ 2) * u r ^ 2) ≤
      48 * (∫ r in a..b, w r * du r ^ 2 + J * dw r / r * u r ^ 2) -
        24 * ((w b / b) * u b ^ 2 - (w a / a) * u a ^ 2) := by
  let boundary := fun r => (w r / r) * u r ^ 2
  let dboundary := fun r => ((dw r * r - w r) / r ^ 2) * u r ^ 2 +
    (w r / r) * (2 * u r * du r)
  let energy := fun r => w r * du r ^ 2 + J * dw r / r * u r ^ 2
  let mass := fun r => (12 * w r / r ^ 2) * u r ^ 2
  have hrpos (r : ℝ) (hr : r ∈ Icc a b) : 0 < r := ha.trans_le hr.1
  have hne (r : ℝ) (hr : r ∈ Icc a b) : r ≠ 0 := (hrpos r hr).ne'
  have hne₂ (r : ℝ) (hr : r ∈ Icc a b) : r ^ 2 ≠ 0 := pow_ne_zero 2 (hne r hr)
  have hid : ContinuousOn (fun r : ℝ => r) (Icc a b) := continuousOn_id
  have hbc : ContinuousOn boundary (Icc a b) := (hwc.div hid hne).mul (huc.pow 2)
  have hdbc : ContinuousOn dboundary (Icc a b) :=
    ((((hdwc.mul hid).sub hwc).div (hid.pow 2) hne₂).mul (huc.pow 2)).add
      ((hwc.div hid hne).mul ((huc.const_mul 2).mul hduc))
  have hec : ContinuousOn energy (Icc a b) :=
    (hwc.mul (hduc.pow 2)).add (((hdwc.const_mul J).div hid hne).mul (huc.pow 2))
  have hmc : ContinuousOn mass (Icc a b) :=
    ((hwc.const_mul 12).div (hid.pow 2) hne₂).mul (huc.pow 2)
  have hbd (r : ℝ) (hr : r ∈ Ioo a b) : HasDerivAt boundary (dboundary r) r := by
    have h := ((hw r hr).div (hasDerivAt_id r) (hne r (Ioo_subset_Icc_self hr))).mul
      ((hu r hr).pow 2)
    simpa only [boundary, dboundary, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one] using h
  have hbint := hdbc.intervalIntegrable_of_Icc hab
  have heint := hec.intervalIntegrable_of_Icc hab
  have hmint := hmc.intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hbc hbd hbint
  have hpoint (r : ℝ) (hr : r ∈ Icc a b) : mass r ≤ 48 * energy r - 24 * dboundary r := by
    have hrp := hrpos r hr
    have hwp := hwn r hr
    have hdwp := hdwn r hr
    have hJp : 0 ≤ J - 1 / 2 := sub_nonneg.mpr hJ
    have hrem : 0 ≤ 48 * (w r * (du r - u r / (2 * r)) ^ 2 +
        (J - 1 / 2) * (dw r / r) * u r ^ 2) := by positivity
    have heq : (48 * energy r - 24 * dboundary r) - mass r =
        48 * (w r * (du r - u r / (2 * r)) ^ 2 +
          (J - 1 / 2) * (dw r / r) * u r ^ 2) := by
      dsimp only [energy, dboundary, mass]
      field_simp [hrp.ne'] <;> ring
    linarith only [heq, hrem]
  have hmono := intervalIntegral.integral_mono_on hab hmint
    ((heint.const_mul 48).sub (hbint.const_mul 24)) hpoint
  change (∫ r in a..b, mass r) ≤ 48 * (∫ r in a..b, energy r) -
    24 * (boundary b - boundary a)
  calc
    _ ≤ ∫ r in a..b, 48 * energy r - 24 * dboundary r := hmono
    _ = _ := by
      rw [intervalIntegral.integral_sub (heint.const_mul 48) (hbint.const_mul 24),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hftc]

/-- The right endpoint term is nonpositive and can be dropped. The
remaining left trace is the actual weighted trace of the same function. -/
theorem radialPositiveHardy_mass_le_energy_left {a b j : ℝ} {w u : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hwn : ∀ r ∈ Icc a b, 0 ≤ w r)
    (hdwn : ∀ r ∈ Icc a b, 0 ≤ deriv w r) (hj : 1 / 2 ≤ j ^ 2) :
    (∫ r in a..b, (12 * w r / r ^ 2) * u r ^ 2) ≤
      48 * (∫ r in a..b, w r * deriv u r ^ 2 + j ^ 2 * deriv w r / r * u r ^ 2) +
        24 * (w a / a) * u a ^ 2 := by
  have hdwc := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hduc := (contDiff_infty_iff_deriv.mp hu).2.continuous
  have h := radialPositiveHardy_boundary hab ha hw.continuous.continuousOn
    hdwc.continuousOn hu.continuous.continuousOn hduc.continuousOn
    (fun r _ => (hw.differentiable (by simp) r).hasDerivAt)
    (fun r _ => (hu.differentiable (by simp) r).hasDerivAt) hwn hdwn hj
  have hb : 0 ≤ (w b / b) * u b ^ 2 :=
    mul_nonneg (div_nonneg (hwn b ⟨hab, le_rfl⟩) (ha.trans_le hab).le) (sq_nonneg _)
  linarith only [h, hb]

/-- A zero left trace gives a universal Dirichlet coercivity constant,
even when the positive logarithmic slope has no uniform lower bound. -/
theorem radialPositiveHardy_dirichlet {a b j : ℝ} {w u : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hwn : ∀ r ∈ Icc a b, 0 ≤ w r)
    (hdwn : ∀ r ∈ Icc a b, 0 ≤ deriv w r) (hj : 1 / 2 ≤ j ^ 2) (hua : u a = 0) :
    (∫ r in a..b, (12 * w r / r ^ 2) * u r ^ 2) ≤
      48 * (∫ r in a..b, w r * deriv u r ^ 2 + j ^ 2 * deriv w r / r * u r ^ 2) := by
  simpa only [hua, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
    radialPositiveHardy_mass_le_energy_left hab ha hw hu hwn hdwn hj

end ContinuousFlexibility.Radial
