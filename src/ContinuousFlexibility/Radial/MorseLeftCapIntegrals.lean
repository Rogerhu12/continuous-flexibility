import ContinuousFlexibility.Radial.MorseChainParameters
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual coefficient moments on the Morse mass interval

The interval starts at the fixed cut `-log(3/2)` and ends at the
actual right zero of the Morse coefficient. The finite-interval
identities retain the end terms. They are independent of radius
positivity and of the subsequent short join.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

def morseCellLeftCut : ℝ := -log (3 / 2)

def morseLeftMassLength (A B : ℝ) : ℝ := morseRightTurn A B - morseCellLeftCut

theorem exp_neg_morseCellLeftCut : exp (-morseCellLeftCut) = 3 / 2 := by
  rw [morseCellLeftCut, neg_neg, exp_log (by norm_num : (0 : ℝ) < 3 / 2)]

theorem morseCellLeftCut_lt_rightTurn {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    morseCellLeftCut < morseRightTurn A B := by
  have hc : morseCellLeftCut < 0 := neg_neg_of_pos (log_pos (by norm_num))
  have hb := morseRootT_bounds hB hAB
  have ht : 0 < morseRightTurn A B := neg_pos.mpr (log_neg hb.1 (hb.2.1.trans (by norm_num)))
  exact hc.trans ht

theorem morseLeftMassLength_log_le {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    morseLeftMassLength A B ≤ log (A / B) + log (3 / 2) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have he : -log (B / A) = log (A / B) := by
    rw [log_div hB.ne' hA.ne', log_div hA.ne' hB.ne']
    ring
  have hx := (morseRightTurn_log_bounds hB hAB).2.trans_eq he
  unfold morseLeftMassLength morseCellLeftCut
  linarith only [hx]

theorem morseLeftMassLength_le_hundred_div {A B : ℝ}
    (hA1 : A ≤ 1) (hB : 0 < B) (hAB : 4 * B < A) (hBA : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) :
    morseLeftMassLength A B ≤ 100 / A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hq : A / B ≤ (9 : ℝ) ^ 9 / A ^ 8 := by
    apply (div_le_iff₀ hB).mpr
    calc
      A = ((9 : ℝ) ^ 9 / A ^ 8) * (A ^ 9 / (9 : ℝ) ^ 9) := by
        field_simp [hA.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hBA (by positivity)
  have hl := log_le_log (div_pos hA hB) hq
  rw [log_div (pow_ne_zero _ (by norm_num : (9 : ℝ) ≠ 0)) (pow_ne_zero _ hA.ne'),
    log_pow, log_pow] at hl
  have h9 : log 9 ≤ 8 := by
    simpa only [show (9 : ℝ) - 1 = 8 by norm_num] using log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
  have hc : log (3 / 2) ≤ (1 / 2 : ℝ) := by
    simpa only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have hinv : 1 ≤ A⁻¹ := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le hA hA1
  have hlog : -log A ≤ A⁻¹ := by
    have hh := log_le_sub_one_of_pos (inv_pos.mpr hA)
    rw [log_inv] at hh
    linarith only [hh]
  rw [div_eq_mul_inv]
  linarith only [morseLeftMassLength_log_le hB hAB, hl, h9, hc, hinv, hlog]

private theorem hasDerivAt_decay (k x : ℝ) :
    HasDerivAt (fun y : ℝ => exp (-k * y)) (-k * exp (-k * x)) x := by
  have h := ((hasDerivAt_id x).const_mul (-k)).exp
  change HasDerivAt (fun y : ℝ => exp (-k * y)) _ x at h
  apply h.congr_deriv
  change exp (-k * x) * (-k * 1) = -k * exp (-k * x)
  ring

private theorem continuous_decay (k : ℝ) : Continuous (fun y : ℝ => exp (-k * y)) :=
  (continuous_const.mul continuous_id).rexp

private theorem decay_integral (a b k : ℝ) (hk : 0 < k) :
    (∫ y in a..b, exp (-k * y)) = (exp (-k * a) - exp (-k * b)) / k := by
  have hder (x : ℝ) : HasDerivAt (fun y : ℝ => -exp (-k * y) / k) (exp (-k * x)) x := by
    apply (((hasDerivAt_decay k x).neg).div_const k).congr_deriv
    calc
      -(-k * exp (-k * x)) / k = k * exp (-k * x) / k := by ring
      _ = _ := mul_div_cancel_left₀ _ hk.ne'
  calc
    _ = -exp (-k * b) / k - (-exp (-k * a) / k) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
        ((continuous_decay k).intervalIntegrable a b)
    _ = _ := by ring

private theorem decay_first_moment (a b k : ℝ) (hk : 0 < k) :
    (∫ y in a..b, (y - a) * exp (-k * y)) =
      exp (-k * a) / k ^ 2 - ((b - a) / k + 1 / k ^ 2) * exp (-k * b) := by
  let P : ℝ → ℝ := fun y => -((y - a) / k + 1 / k ^ 2) * exp (-k * y)
  have hder (x : ℝ) : HasDerivAt P ((x - a) * exp (-k * x)) x := by
    have hlin := (((hasDerivAt_id x).sub_const a).div_const k).add_const (1 / k ^ 2)
    have h := hlin.neg.mul (hasDerivAt_decay k x)
    change HasDerivAt P _ x at h
    apply h.congr_deriv
    change -(1 / k) * exp (-k * x) +
      -((x - a) / k + 1 / k ^ 2) * (-k * exp (-k * x)) = (x - a) * exp (-k * x)
    field_simp [hk.ne']
    all_goals ring
  have hc : Continuous (fun y : ℝ => (y - a) * exp (-k * y)) :=
    (continuous_id.sub continuous_const).mul (continuous_decay k)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x) (hc.intervalIntegrable a b)]
  dsimp only [P]
  ring

private theorem exp_neg_twice (x : ℝ) : exp (-2 * x) = exp (-x) ^ 2 := by
  rw [pow_two, ← exp_add]
  congr 1
  ring

private theorem left_exp_one {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    (∫ y in morseCellLeftCut..morseRightTurn A B, exp (-y)) = 3 / 2 - morseRightRootT A B := by
  simpa only [neg_one_mul, div_one, exp_neg_morseCellLeftCut, exp_neg_morseRightTurn hB hAB] using
    decay_integral morseCellLeftCut (morseRightTurn A B) 1 (by norm_num)

private theorem left_exp_two {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    (∫ y in morseCellLeftCut..morseRightTurn A B, exp (-2 * y)) =
      (9 / 4 - morseRightRootT A B ^ 2) / 2 := by
  rw [decay_integral _ _ 2 (by norm_num), exp_neg_twice, exp_neg_twice,
    exp_neg_morseCellLeftCut, exp_neg_morseRightTurn hB hAB]
  norm_num

private theorem left_moment_one {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    (∫ y in morseCellLeftCut..morseRightTurn A B, (y - morseCellLeftCut) * exp (-y)) =
      3 / 2 - (morseLeftMassLength A B + 1) * morseRightRootT A B := by
  simpa only [morseLeftMassLength, neg_one_mul, one_pow, div_one, exp_neg_morseCellLeftCut,
    exp_neg_morseRightTurn hB hAB] using
    decay_first_moment morseCellLeftCut (morseRightTurn A B) 1 (by norm_num)

private theorem left_moment_two {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    (∫ y in morseCellLeftCut..morseRightTurn A B, (y - morseCellLeftCut) * exp (-2 * y)) =
      9 / 16 - (morseLeftMassLength A B / 2 + 1 / 4) * morseRightRootT A B ^ 2 := by
  rw [decay_first_moment _ _ 2 (by norm_num), exp_neg_twice, exp_neg_twice,
    exp_neg_morseCellLeftCut, exp_neg_morseRightTurn hB hAB]
  norm_num [morseLeftMassLength]

private theorem interval_first_moment (a b : ℝ) :
    (∫ y in a..b, y - a) = (b - a) ^ 2 / 2 := by
  have hder (x : ℝ) : HasDerivAt (fun y : ℝ => (y - a) ^ 2 / 2) (x - a) x := by
    apply ((((hasDerivAt_id x).sub_const a).pow 2).div_const 2).congr_deriv
    change (2 * (x - a) ^ (2 - 1) * 1) / 2 = x - a
    norm_num
  simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
      ((continuous_id.sub continuous_const).intervalIntegrable a b)

private theorem continuous_morse_coefficient (A B : ℝ) : Continuous (morseRho A B) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_morseRho A B x).continuousAt

private theorem continuous_exp_neg : Continuous (fun y : ℝ => exp (-y)) :=
  continuous_neg.rexp

theorem abs_morseRho_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℝ) :
    |morseRho A B x| ≤ A * (exp (-x) + exp (-2 * x)) + B := by
  unfold morseRho
  have ht : |exp (-x) - exp (-2 * x)| ≤ exp (-x) + exp (-2 * x) := by
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_pos (exp_pos _)] using
      (abs_sub_le (exp (-x)) 0 (exp (-2 * x)))
  calc
    _ ≤ |A * (exp (-x) - exp (-2 * x))| + B := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hB] using
        (abs_sub_le (A * (exp (-x) - exp (-2 * x))) 0 B)
    _ = A * |exp (-x) - exp (-2 * x)| + B := by rw [abs_mul, abs_of_nonneg hA]
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left ht hA) B

private theorem interval_weight_morse_eq (A B a b : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ y in a..b, w y * morseRho A B y) =
      A * ((∫ y in a..b, w y * exp (-y)) - (∫ y in a..b, w y * exp (-2 * y))) -
        B * (∫ y in a..b, w y) := by
  have h₁ : Continuous (fun y => w y * exp (-y)) := hw.mul continuous_exp_neg
  have h₂ : Continuous (fun y => w y * exp (-2 * y)) := hw.mul (continuous_decay 2)
  have hL : Continuous (fun y => A * (w y * exp (-y) - w y * exp (-2 * y))) :=
    continuous_const.mul (h₁.sub h₂)
  have hR : Continuous (fun y => B * w y) := continuous_const.mul hw
  have heq : (fun y => w y * morseRho A B y) =
      (fun y => A * (w y * exp (-y) - w y * exp (-2 * y)) - B * w y) := by
    funext y
    unfold morseRho
    ring
  rw [heq, intervalIntegral.integral_sub (hL.intervalIntegrable a b) (hR.intervalIntegrable a b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (h₁.intervalIntegrable a b) (h₂.intervalIntegrable a b)]

private theorem interval_weight_abs_morse_le {A B a b : ℝ} {w : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hab : a ≤ b) (hw : Continuous w)
    (hwp : ∀ y ∈ Icc a b, 0 ≤ w y) :
    (∫ y in a..b, w y * |morseRho A B y|) ≤
      A * ((∫ y in a..b, w y * exp (-y)) + (∫ y in a..b, w y * exp (-2 * y))) +
        B * (∫ y in a..b, w y) := by
  have h₁ : Continuous (fun y => w y * exp (-y)) := hw.mul continuous_exp_neg
  have h₂ : Continuous (fun y => w y * exp (-2 * y)) := hw.mul (continuous_decay 2)
  have hL : Continuous (fun y => A * (w y * exp (-y) + w y * exp (-2 * y))) :=
    continuous_const.mul (h₁.add h₂)
  have hR : Continuous (fun y => B * w y) := continuous_const.mul hw
  have hf := hw.mul (continuous_morse_coefficient A B).abs
  calc
    _ ≤ ∫ y in a..b, A * (w y * exp (-y) + w y * exp (-2 * y)) + B * w y := by
      apply intervalIntegral.integral_mono_on hab (hf.intervalIntegrable a b)
        ((hL.add hR).intervalIntegrable a b)
      intro y hy
      calc
        _ ≤ w y * (A * (exp (-y) + exp (-2 * y)) + B) :=
          mul_le_mul_of_nonneg_left (abs_morseRho_le hA hB y) (hwp y hy)
        _ = _ := by
          change w y * (A * (exp (-y) + exp (-2 * y)) + B) =
            A * (w y * exp (-y) + w y * exp (-2 * y)) + B * w y
          ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hL.intervalIntegrable a b) (hR.intervalIntegrable a b),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (h₁.intervalIntegrable a b) (h₂.intervalIntegrable a b)]

private theorem left_integral_one (A B : ℝ) :
    (∫ _ in morseCellLeftCut..morseRightTurn A B, (1 : ℝ)) = morseLeftMassLength A B := by
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, morseLeftMassLength]

theorem morseLeftMass_integral {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    (∫ y in morseCellLeftCut..morseRightTurn A B, morseRho A B y) =
      (3 / 8) * A - A * (morseRightRootT A B - morseRightRootT A B ^ 2 / 2) -
        B * morseLeftMassLength A B := by
  have h := interval_weight_morse_eq A B morseCellLeftCut (morseRightTurn A B)
    (w := fun _ => 1) continuous_const
  simp only [one_mul, left_exp_one hB hAB, left_exp_two hB hAB, left_integral_one] at h
  rw [h]
  ring

theorem morseLeftMass_first_moment {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    (∫ y in morseCellLeftCut..morseRightTurn A B, (y - morseCellLeftCut) * morseRho A B y) =
      (15 / 16) * A -
        A * ((morseLeftMassLength A B + 1) * morseRightRootT A B -
          (morseLeftMassLength A B / 2 + 1 / 4) * morseRightRootT A B ^ 2) -
        B * (morseLeftMassLength A B ^ 2 / 2) := by
  rw [interval_weight_morse_eq A B _ _ (w := fun y => y - morseCellLeftCut)
      (continuous_id.sub continuous_const),
    left_moment_one hB hAB, left_moment_two hB hAB, interval_first_moment]
  unfold morseLeftMassLength
  ring

theorem morseLeftMass_abs_integral_le {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    (∫ y in morseCellLeftCut..morseRightTurn A B, |morseRho A B y|) ≤
      (21 / 8) * A + B * morseLeftMassLength A B := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have ht := (morseRootT_bounds hB hAB).1
  have h := interval_weight_abs_morse_le hA.le hB.le (morseCellLeftCut_lt_rightTurn hB hAB).le
    (w := fun _ => 1) continuous_const (fun _ _ => zero_le_one)
  simp only [one_mul, left_exp_one hB hAB, left_exp_two hB hAB, left_integral_one] at h
  have hsum : (3 / 2 - morseRightRootT A B) + (9 / 4 - morseRightRootT A B ^ 2) / 2 ≤ 21 / 8 := by
    nlinarith only [ht.le, sq_nonneg (morseRightRootT A B)]
  exact h.trans ((add_le_add_left (mul_le_mul_of_nonneg_left hsum hA.le) _).trans_eq
    (by rw [mul_comm A (21 / 8)]))

theorem morseLeftMass_abs_first_moment_le {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    (∫ y in morseCellLeftCut..morseRightTurn A B,
      (y - morseCellLeftCut) * |morseRho A B y|) ≤
      (33 / 16) * A + B * (morseLeftMassLength A B ^ 2 / 2) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 ≤ morseLeftMassLength A B := sub_nonneg.mpr (morseCellLeftCut_lt_rightTurn hB hAB).le
  have h := interval_weight_abs_morse_le hA.le hB.le (morseCellLeftCut_lt_rightTurn hB hAB).le
    (w := fun y => y - morseCellLeftCut)
    (continuous_id.sub continuous_const) (fun _ hy => sub_nonneg.mpr hy.1)
  rw [left_moment_one hB hAB, left_moment_two hB hAB, interval_first_moment] at h
  have ht := (morseRootT_bounds hB hAB).1
  have hsum : (3 / 2 - (morseLeftMassLength A B + 1) * morseRightRootT A B) +
      (9 / 16 - (morseLeftMassLength A B / 2 + 1 / 4) * morseRightRootT A B ^ 2) ≤ 33 / 16 := by
    linarith only [mul_nonneg (by linarith : 0 ≤ morseLeftMassLength A B + 1) ht.le,
      mul_nonneg (by linarith : 0 ≤ morseLeftMassLength A B / 2 + 1 / 4)
        (sq_nonneg (morseRightRootT A B))]
  exact h.trans ((add_le_add_left (mul_le_mul_of_nonneg_left hsum hA.le) _).trans_eq
    (by rw [morseLeftMassLength, mul_comm A (33 / 16)]))

theorem morseLeftMass_abs_integral_from_le {A B x : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hx : x ∈ Icc morseCellLeftCut (morseRightTurn A B)) :
    (∫ y in x..morseRightTurn A B, |morseRho A B y|) ≤
      (21 / 8) * A + B * morseLeftMassLength A B := by
  apply le_trans _ (morseLeftMass_abs_integral_le hB hAB)
  exact intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    ((continuous_morse_coefficient A B).abs.intervalIntegrable _ _)

theorem morseLeftMass_abs_first_moment_from_le {A B x : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hx : x ∈ Icc morseCellLeftCut (morseRightTurn A B)) :
    (∫ y in x..morseRightTurn A B, (y - x) * |morseRho A B y|) ≤
      (33 / 16) * A + B * (morseLeftMassLength A B ^ 2 / 2) := by
  have hρ := (continuous_morse_coefficient A B).abs
  have hX : Continuous (fun y => (y - x) * |morseRho A B y|) :=
    (continuous_id.sub continuous_const).mul hρ
  have hC : Continuous (fun y => (y - morseCellLeftCut) * |morseRho A B y|) :=
    (continuous_id.sub continuous_const).mul hρ
  calc
    _ ≤ ∫ y in x..morseRightTurn A B, (y - morseCellLeftCut) * |morseRho A B y| :=
      intervalIntegral.integral_mono_on hx.2 (hX.intervalIntegrable _ _) (hC.intervalIntegrable _ _)
        (fun _ _ => mul_le_mul_of_nonneg_right (sub_le_sub_left hx.1 _) (abs_nonneg _))
    _ ≤ ∫ y in morseCellLeftCut..morseRightTurn A B, (y - morseCellLeftCut) * |morseRho A B y| := by
      apply intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl _ (hC.intervalIntegrable _ _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact mul_nonneg (sub_nonneg.mpr hy.1.le) (abs_nonneg _)
    _ ≤ _ := morseLeftMass_abs_first_moment_le hB hAB

private theorem morse_mul_right_root_le {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    A * morseRightRootT A B ≤ 2 * B := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hcancel : A * (B / A) = B := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hA.ne']
  calc
    _ ≤ A * (2 * (B / A)) := mul_le_mul_of_nonneg_left (morseRightRootT_ratio_bounds hB hAB).2 hA.le
    _ = _ := by rw [mul_left_comm A 2, hcancel]

theorem morseLeftMass_integral_error {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    |(∫ y in morseCellLeftCut..morseRightTurn A B, morseRho A B y) - (3 / 8) * A| ≤
      2 * B + B * morseLeftMassLength A B := by
  let t := morseRightRootT A B
  let L := morseLeftMassLength A B
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 ≤ L := sub_nonneg.mpr (morseCellLeftCut_lt_rightTurn hB hAB).le
  have ht : 0 < t := (morseRootT_bounds hB hAB).1
  have ht₁ : t ≤ 1 / 2 := (morseRootT_bounds hB hAB).2.1.le
  have htail : 0 ≤ t - t ^ 2 / 2 := by
    nlinarith only [mul_nonneg ht.le (by linarith : 0 ≤ 2 - t)]
  rw [morseLeftMass_integral hB hAB]
  change |(3 / 8) * A - A * (t - t ^ 2 / 2) - B * L - (3 / 8) * A| ≤ 2 * B + B * L
  rw [show (3 / 8) * A - A * (t - t ^ 2 / 2) - B * L - (3 / 8) * A =
    -(A * (t - t ^ 2 / 2) + B * L) by ring, abs_neg,
    abs_of_nonneg (add_nonneg (mul_nonneg hA.le htail) (mul_nonneg hB.le hL))]
  exact add_le_add_left
    ((mul_le_mul_of_nonneg_left (sub_le_self _ (div_nonneg (sq_nonneg t) (by norm_num))) hA.le).trans
      (morse_mul_right_root_le hB hAB)) _

theorem morseLeftMass_first_moment_error {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    |(∫ y in morseCellLeftCut..morseRightTurn A B, (y - morseCellLeftCut) * morseRho A B y) -
      (15 / 16) * A| ≤
      2 * B * (morseLeftMassLength A B + 1) + B * (morseLeftMassLength A B ^ 2 / 2) := by
  let t := morseRightRootT A B
  let L := morseLeftMassLength A B
  let u := (L + 1) * t
  let v := (L / 2 + 1 / 4) * t ^ 2
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 ≤ L := sub_nonneg.mpr (morseCellLeftCut_lt_rightTurn hB hAB).le
  have ht : 0 < t := (morseRootT_bounds hB hAB).1
  have ht₁ : t ≤ 1 / 2 := (morseRootT_bounds hB hAB).2.1.le
  have htsq : t ^ 2 ≤ t := by
    nlinarith only [mul_nonneg ht.le (by linarith : 0 ≤ 1 - t)]
  have hc : 0 ≤ L / 2 + 1 / 4 := by linarith
  have hv0 : 0 ≤ v := mul_nonneg hc (sq_nonneg t)
  have hv : v ≤ u := by
    calc
      _ ≤ (L / 2 + 1 / 4) * t := mul_le_mul_of_nonneg_left htsq hc
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) ht.le
  rw [morseLeftMass_first_moment hB hAB]
  change |(15 / 16) * A - A * (u - v) - B * (L ^ 2 / 2) - (15 / 16) * A| ≤
    2 * B * (L + 1) + B * (L ^ 2 / 2)
  rw [show (15 / 16) * A - A * (u - v) - B * (L ^ 2 / 2) - (15 / 16) * A =
    -(A * (u - v) + B * (L ^ 2 / 2)) by ring, abs_neg,
    abs_of_nonneg (add_nonneg (mul_nonneg hA.le (sub_nonneg.mpr hv))
      (mul_nonneg hB.le (div_nonneg (sq_nonneg L) (by norm_num))))]
  apply add_le_add_left
  calc
    _ ≤ A * u := mul_le_mul_of_nonneg_left (sub_le_self _ hv0) hA.le
    _ = (A * t) * (L + 1) := by dsimp only [u]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (morse_mul_right_root_le hB hAB) (by linarith)

end ContinuousFlexibility.Radial
