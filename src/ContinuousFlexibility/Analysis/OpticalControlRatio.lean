import ContinuousFlexibility.Analysis.StateControlDecay
import ContinuousFlexibility.Analysis.OpticalControlCurvature
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A continuous control ratio at simple turning points

The support condition in N01 permits the closed support to meet a turning
point.  Smoothness still makes every control jet vanish there.  Dividing
the first control jet by the simple zero of the profile slope therefore
has a continuous extension, with value zero at both endpoints.  This
turns the optical radicand into a fixed nonnegative factor times a
uniformly positive parameter factor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

/-- Two actual difference quotients remove a simple denominator zero.
The numerator has zero first derivative, so ordinary division already
assigns the correct continuous value at the zero. -/
theorem continuousAt_div_of_simple_zero
    {u q : ℝ → ℝ} {a d : ℝ} (hu : HasDerivAt u 0 a)
    (hq : HasDerivAt q d a) (hu0 : u a = 0) (hq0 : q a = 0) (hd : d ≠ 0) :
    ContinuousAt (fun r => u r / q r) a := by
  classical
  have hc := hu.continuousAt_div.div hq.continuousAt_div
    (by simpa using hd)
  have heq :
      (Function.update (fun x => (u x - u a) / (x - a)) a 0 /
        Function.update (fun x => (q x - q a) / (x - a)) a d) =
      (fun r => u r / q r) := by
    funext r
    change Function.update (fun x => (u x - u a) / (x - a)) a 0 r /
      Function.update (fun x => (q x - q a) / (x - a)) a d r = u r / q r
    by_cases hra : r = a
    · simp [hra, hu0, hq0]
    · by_cases hqr : q r = 0
      · simp [Function.update, hra, Ne.symm hra, hu0, hq0, hqr]
      · simp [Function.update, hra, Ne.symm hra, hu0, hq0]
        <;> field_simp [hqr, sub_ne_zero.mpr hra]
        <;> ring
  rw [heq] at hc
  exact hc

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

theorem control_first_second_deriv_zero_off_interval
    {χ : ℝ → ℝ} {l h r : ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsupp : Function.support χ ⊆ Ioo l h) (hr : r ∉ Ioo l h) :
    deriv χ r = 0 ∧ deriv (deriv χ) r = 0 := by
  constructor
  · simpa only [iteratedDeriv_one] using
      iteratedDeriv_zero_off_open_interval hχ hsupp 1 hr
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      iteratedDeriv_zero_off_open_interval hχ hsupp 2 hr

def opticalLogRatio (w χ : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv χ r * w r / deriv w r

theorem continuousOn_opticalLogRatio
    {w χ : ℝ → ℝ} {l h : ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hturn : deriv w l = 0 ∧ deriv w h = 0 ∧
      deriv (deriv w) l ≠ 0 ∧ deriv (deriv w) h ≠ 0)
    (hsupp : Function.support χ ⊆ Ioo l h) :
    ContinuousOn (opticalLogRatio w χ) (Icc l h) := by
  have hwd := (contDiff_infty_iff_deriv.mp hw).2
  have hχd := (contDiff_infty_iff_deriv.mp hχ).2
  have hend (a : ℝ) (ha : a ∉ Ioo l h) (hwa : deriv w a = 0)
      (hwda : deriv (deriv w) a ≠ 0) :
      ContinuousAt (opticalLogRatio w χ) a := by
    obtain ⟨hχ1, hχ2⟩ := control_first_second_deriv_zero_off_interval hχ hsupp ha
    have hn : HasDerivAt (fun r => deriv χ r * w r) 0 a := by
      have hp := (hχd.differentiable (by simp) a).hasDerivAt.mul
        (hw.differentiable (by simp) a).hasDerivAt
      have hp' : HasDerivAt (fun r => deriv χ r * w r)
          (deriv (deriv χ) a * w a + deriv χ a * deriv w a) a :=
        hp.congr_of_eventuallyEq (Eventually.of_forall (fun _ => rfl))
      simpa only [hχ1, hχ2, zero_mul, zero_add] using hp'
    exact Analysis.continuousAt_div_of_simple_zero hn
      (hwd.differentiable (by simp) a).hasDerivAt
      (by simp only [hχ1, zero_mul]) hwa hwda
  intro r hr
  by_cases hrl : r = l
  · subst r
    exact (hend l (by simp) hturn.1 hturn.2.2.1).continuousWithinAt
  by_cases hrh : r = h
  · subst r
    exact (hend h (by simp) hturn.2.1 hturn.2.2.2).continuousWithinAt
  have hri : r ∈ Ioo l h :=
    ⟨lt_of_le_of_ne hr.1 (Ne.symm hrl), lt_of_le_of_ne hr.2 hrh⟩
  exact ((hχd.continuous.continuousAt.mul hw.continuous.continuousAt).div
    hwd.continuous.continuousAt (hneg r hri).ne).continuousWithinAt

theorem optical_radical_nonneg_on_component
    {w : ℝ → ℝ} {l h : ℝ} (hl : 0 < l)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hturn : deriv w l = 0 ∧ deriv w h = 0)
    {r : ℝ} (hr : r ∈ Icc l h) :
    0 ≤ -deriv w r / (r * w r) := by
  have hslope : deriv w r ≤ 0 := by
    by_cases hrl : r = l
    · simpa only [hrl, hturn.1] using (le_refl (0 : ℝ))
    by_cases hrh : r = h
    · simpa only [hrh, hturn.2] using (le_refl (0 : ℝ))
    exact (hneg r ⟨lt_of_le_of_ne hr.1 (Ne.symm hrl), lt_of_le_of_ne hr.2 hrh⟩).le
  exact div_nonneg (neg_nonneg.mpr hslope)
    (mul_pos (hl.trans_le hr.1) (hpos r hr)).le

/-- The factorization is exact, including both turning points.  In
particular no compact interior collar is being assumed. -/
theorem opticalSpeed_logPerturbation_factor
    {w χ : ℝ → ℝ} {l h t r : ℝ} (hl : 0 < l)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hturn : deriv w l = 0 ∧ deriv w h = 0)
    (hsupp : Function.support χ ⊆ Ioo l h) (hr : r ∈ Icc l h) :
    opticalSpeed (opticalLogPerturbation w χ t) r =
      opticalSpeed w r * Real.sqrt (1 + t * opticalLogRatio w χ r) := by
  have hr0 : r ≠ 0 := (hl.trans_le hr.1).ne'
  have hw0 : w r ≠ 0 := (hpos r hr).ne'
  rw [opticalSpeed_logPerturbation_affine
    (hw.differentiable (by simp) r) (hχ.differentiable (by simp) r) hr0 hw0]
  have hrad :
      -deriv w r / (r * w r) + t * (-deriv χ r / r) =
        (-deriv w r / (r * w r)) * (1 + t * opticalLogRatio w χ r) := by
    by_cases hrl : r = l
    · subst r
      have hz := (control_first_second_deriv_zero_off_interval hχ hsupp (r := l) (by simp)).1
      simp only [hturn.1, hz, neg_zero, zero_div, mul_zero, zero_mul, add_zero]
    by_cases hrh : r = h
    · subst r
      have hz := (control_first_second_deriv_zero_off_interval hχ hsupp (r := h) (by simp)).1
      simp only [hturn.2, hz, neg_zero, zero_div, mul_zero, zero_mul, add_zero]
    have hwr : deriv w r ≠ 0 :=
      (hneg r ⟨lt_of_le_of_ne hr.1 (Ne.symm hrl), lt_of_le_of_ne hr.2 hrh⟩).ne
    dsimp only [opticalLogRatio]
    field_simp [hr0, hw0, hwr]
    <;> ring
  rw [hrad, Real.sqrt_mul (optical_radical_nonneg_on_component hl hpos hneg hturn hr)]
  rfl

theorem opticalTravel_logPerturbation_factor
    {w χ : ℝ → ℝ} {l h : ℝ} (hl : 0 < l) (hlh : l < h)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hturn : deriv w l = 0 ∧ deriv w h = 0)
    (hsupp : Function.support χ ⊆ Ioo l h) (t : ℝ) :
    opticalTravel (opticalLogPerturbation w χ t) l h =
      ∫ r in l..h, opticalSpeed w r * Real.sqrt (1 + t * opticalLogRatio w χ r) := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hlh.le] at hr
  exact opticalSpeed_logPerturbation_factor hl hw hχ hpos hneg hturn hsupp hr

end ContinuousFlexibility.Statements
