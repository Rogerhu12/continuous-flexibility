import ContinuousFlexibility.Radial.OuterMorseCellEnergy
import ContinuousFlexibility.Radial.OuterFrequencyScale

/-!
# The frequency-band size of the actual cell transfer factor

The long right cap is estimated by its balanced coefficient product.
Its large length contributes only to the polynomial prefactor, whose
logarithm is quadratic in the cell index.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

theorem outer_exp_pow_four (x : ℝ) : exp x ^ 4 = exp (4 * x) := by
  calc
    _ = (exp x * exp x) * (exp x * exp x) := by ring
    _ = exp ((x + x) + (x + x)) := by simp only [exp_add]
    _ = _ := by congr 1; ring

/-- The regularized positive-piece factor only charges its balanced
product to the action; a fixed prefactor is absorbed quadratically. -/
theorem outer_positive_factor_le_exp {a b A j K M P N : ℝ}
    (hN : 1 ≤ N) (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 ≤ A) (hj : 0 ≤ j)
    (hbase : 0 ≤ 1 + a + b)
    (hsize : 1 + a + b ≤ M * exp (P * N))
    (hprod : a * b ≤ K * j ^ 2 * A) :
    (1 + a + b) ^ 4 * exp (2 * sqrt (a * b) + 2) ≤
      exp ((4 * (M + P) + 2) * N + 2 * sqrt K * (j * sqrt A)) := by
  have hMexp : M ≤ exp (M * N) :=
    (le_mul_of_one_le_right hM hN).trans
      ((le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _))
  have hsum : 1 + a + b ≤ exp ((M + P) * N) := by
    calc
      _ ≤ M * exp (P * N) := hsize
      _ ≤ exp (M * N) * exp (P * N) :=
        mul_le_mul_of_nonneg_right hMexp (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hroot : sqrt (a * b) ≤ sqrt K * (j * sqrt A) := by
    calc
      _ ≤ sqrt (K * j ^ 2 * A) := sqrt_le_sqrt hprod
      _ = _ := by
        rw [sqrt_mul (mul_nonneg hK (sq_nonneg j)), sqrt_mul hK, sqrt_sq hj]
        ring
  calc
    _ ≤ exp ((M + P) * N) ^ 4 *
        exp (2 * (sqrt K * (j * sqrt A)) + 2) :=
      mul_le_mul (pow_le_pow_left₀ hbase hsum 4)
        (exp_le_exp.mpr (by linarith only [hroot])) (exp_pos _).le (by positivity)
    _ = exp (4 * ((M + P) * N) + (2 * (sqrt K * (j * sqrt A)) + 2)) := by
      rw [outer_exp_pow_four, ← exp_add]
    _ ≤ _ := exp_le_exp.mpr (by nlinarith only [hN])

theorem morse_left_cap_coefficient_bounds {A B : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) :
    (0 ≤ morseLeftTurn A B - morseCellLeftCut ∧
      morseLeftTurn A B - morseCellLeftCut ≤ 2) ∧
    (0 ≤ ∫ x in morseCellLeftCut..morseLeftTurn A B, -morseRho A B x) ∧
      (∫ x in morseCellLeftCut..morseLeftTurn A B, -morseRho A B x) ≤ 6 * A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let l := morseCellLeftCut
  let r := morseLeftTurn A B
  have hlr : l ≤ r := (morseCellLeftCut_lt_leftTurn hB hAB).le
  have hlen : r - l ≤ 2 := by
    have hp := (morse_peak_between_turns hB hAB).1
    have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have h3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    dsimp only [r, l, morseCellLeftCut]
    linarith only [hp, h2, h3]
  have hρ₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ -morseRho A B x := by
    rcases hx.2.eq_or_lt with heq | hlt
    · rw [(morseRho_zero_iff_turn hB hAB x).mpr (Or.inl heq)]
      simp
    · exact neg_nonneg.mpr (morseRho_neg_before_left_turn hB hAB hlt).le
  have hρ (x : ℝ) (hx : x ∈ Icc l r) : -morseRho A B x ≤ 3 * A := by
    have he : exp (-x) ≤ 3 / 2 := by
      rw [← exp_neg_morseCellLeftCut]
      exact exp_le_exp.mpr (neg_le_neg hx.1)
    have he₂ := pow_le_pow_left₀ (exp_pos (-x)).le he 2
    have hupper := mul_le_mul_of_nonneg_left he₂ hA.le
    have hpositive := mul_nonneg hA.le (exp_pos (-x)).le
    have heq : exp (-2 * x) = exp (-x) ^ 2 := by
      rw [show -2 * x = -x + -x by ring, exp_add, pow_two]
    unfold morseRho
    rw [heq]
    nlinarith only [hupper, hpositive, hAB, hA]
  have hρc : Continuous (morseRho A B) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_morseRho A B x).continuousAt
  refine ⟨⟨sub_nonneg.mpr hlr, hlen⟩,
    intervalIntegral.integral_nonneg hlr hρ₀, ?_⟩
  calc
    _ ≤ ∫ _x in l..r, 3 * A := intervalIntegral.integral_mono_on hlr
      (hρc.neg.intervalIntegrable l r) (continuous_const.intervalIntegrable l r) hρ
    _ = (r - l) * (3 * A) := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ 2 * (3 * A) := mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = 6 * A := by ring

theorem morse_right_cap_coefficient_bounds {A B : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) (hBA : B ≤ A ^ 9) :
    (0 ≤ ∫ x in morseRightTurn A B..morseRightCapEnd A B (1 / 100), -morseRho A B x) ∧
      (∫ x in morseRightTurn A B..morseRightCapEnd A B (1 / 100), -morseRho A B x) ≤ A ^ 5 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let l := morseRightTurn A B
  let r := morseRightCapEnd A B (1 / 100)
  have hlen : r - l = (1 / 100) / A ^ 4 := by
    dsimp only [l, r, morseRightCapEnd, morseRightCapLength]
    ring
  have hlr : l ≤ r := sub_nonneg.mp (by rw [hlen]; positivity)
  have hρc : Continuous (morseRho A B) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_morseRho A B x).continuousAt
  constructor
  · exact intervalIntegral.integral_nonneg hlr
      (fun x hx => (morseRho_right_cap_bounds hB hAB hx.1).1)
  · calc
      _ ≤ ∫ _x in l..r, B := intervalIntegral.integral_mono_on hlr
        (hρc.neg.intervalIntegrable l r) (continuous_const.intervalIntegrable l r)
        (fun x hx => (morseRho_right_cap_bounds hB hAB hx.1).2)
      _ = (r - l) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ (r - l) * A ^ 9 := mul_le_mul_of_nonneg_left hBA (sub_nonneg.mpr hlr)
      _ = (1 / 100) * A ^ 5 := by rw [hlen]; field_simp [hA.ne'] <;> ring
      _ ≤ A ^ 5 := mul_le_of_le_one_left (by positivity) (by norm_num)

/-- A uniform quantitative estimate for every retained model cell in its
actual frequency band. -/
theorem morse_cell_factor_le_frequency_exp {T : MorseChainData} {C : ℝ} {n j : ℕ}
    (hn : 1 ≤ n) (hd : T.d n = morseChainInteger n)
    (hband : radialFrequencyBand T C n j) :
    morseCellEnergyFactor (morseChainA T n) (morseChainB T n) (j : ℝ) (1 / 100) ≤
      exp ((10 * outerFrequencyExponent C + 500000) * (n : ℝ) ^ 2 +
        10 * ((j : ℝ) * sqrt (morseChainA T n))) := by
  let A := morseChainA T n
  let B := morseChainB T n
  let N := (n : ℝ) ^ 2
  let F := outerFrequencyExponent C
  let tau := (j : ℝ) * sqrt A
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 1 ≤ N := by dsimp only [N]; nlinarith only [hn', sq_nonneg ((n : ℝ) - 1)]
  have hN₀ : 0 ≤ N := zero_le_one.trans hN
  have hF : 0 ≤ F := by dsimp only [F, outerFrequencyExponent]; positivity
  have hd₂ : 2 ≤ (T.d n : ℝ) := by rw [hd]; exact_mod_cast morseChainInteger_ge_two n
  have hpar := morseChainParameters_pos T n hd₂
  have hB : 0 < B := hpar.2
  have hAB : 4 * B < A := hpar.1
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hA9 : A ≤ 9 := morseChainA_le_nine T n hd
  have hBA : B ≤ A ^ 9 := (morseChainB_A_bounds T n (by linarith only [hd₂])).2
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hj2 : (j : ℝ) ^ 2 ≤ exp (F * N) := outer_frequency_sq_le_exp hn hd hband
  have hE : 1 ≤ exp ((F + 4) * N) := one_le_exp_iff.mpr (by positivity)
  have hEF : exp (F * N) ≤ exp ((F + 4) * N) :=
    exp_le_exp.mpr (by nlinarith only [hN₀])
  have hE4 : exp (4 * N) ≤ exp ((F + 4) * N) :=
    exp_le_exp.mpr (by nlinarith only [mul_nonneg hF hN₀])
  have hleft := morse_left_cap_coefficient_bounds hB hAB
  let aL := morseLeftTurn A B - morseCellLeftCut
  let bL := (j : ℝ) ^ 2 * (∫ x in morseCellLeftCut..morseLeftTurn A B, -morseRho A B x)
  have hbL : bL ≤ 54 * exp (F * N) := by
    have hI : (∫ x in morseCellLeftCut..morseLeftTurn A B, -morseRho A B x) ≤ 54 :=
      hleft.2.2.trans (by linarith only [hA9])
    calc
      _ ≤ (j : ℝ) ^ 2 * 54 := mul_le_mul_of_nonneg_left hI (sq_nonneg _)
      _ ≤ exp (F * N) * 54 := mul_le_mul_of_nonneg_right hj2 (by norm_num)
      _ = _ := mul_comm _ _
  have hleftSize : 1 + aL + bL ≤ 60000 * exp ((F + 4) * N) := by
    have hb := hbL.trans (mul_le_mul_of_nonneg_left hEF (by norm_num : (0 : ℝ) ≤ 54))
    nlinarith only [hleft.1.2, hb, hE]
  have hleftProd : aL * bL ≤ 16 * (j : ℝ) ^ 2 * A := by
    have hp := mul_le_mul_of_nonneg_left (morse_left_cap_balanced_product hB hAB) (sq_nonneg (j : ℝ))
    dsimp only [aL, bL]
    nlinarith only [hp, mul_nonneg (sq_nonneg (j : ℝ)) hA.le]
  have hleftFactor :
      morsePositiveEnergyFactor A B (j : ℝ) morseCellLeftCut (morseLeftTurn A B) ≤
        exp ((4 * (60000 + (F + 4)) + 2) * N + 8 * tau) := by
    have hb₀ : 0 ≤ bL := mul_nonneg (sq_nonneg _) hleft.2.1
    have hh := outer_positive_factor_le_exp hN (by norm_num : (0 : ℝ) ≤ 60000)
      (by norm_num : (0 : ℝ) ≤ 16) hA.le hj
      (by linarith only [hleft.1.1, hb₀] : 0 ≤ 1 + aL + bL) hleftSize hleftProd
    have hsqrt : sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num, sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    simpa only [hsqrt, show (2 : ℝ) * 4 = 8 by norm_num,
      morsePositiveEnergyFactor, aL, bL, tau] using hh
  have hright := morse_right_cap_coefficient_bounds hB hAB hBA
  let aR := morseRightCapEnd A B (1 / 100) - morseRightTurn A B
  let bR := (j : ℝ) ^ 2 * (∫ x in morseRightTurn A B..morseRightCapEnd A B (1 / 100), -morseRho A B x)
  have haReq : aR = (1 / 100) / A ^ 4 := by
    dsimp only [aR, morseRightCapEnd, morseRightCapLength]
    ring
  have haR₀ : 0 ≤ aR := by rw [haReq]; positivity
  have hinv : A⁻¹ ≤ 3 * exp N := by
    have hlo : exp (-N) / 3 ≤ A := (morseChainA_exp_bounds T n hd).1
    calc
      _ ≤ (exp (-N) / 3)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le
          (by positivity : 0 < exp (-N) / 3) hlo
      _ = 3 * exp N := by rw [exp_neg]; field_simp [exp_ne_zero N] <;> ring
  have haR : aR ≤ 81 * exp (4 * N) := by
    calc
      _ = (1 / 100) * (A⁻¹) ^ 4 := by
        dsimp only [aR, morseRightCapEnd, morseRightCapLength]
        rw [inv_pow]
        ring
      _ ≤ (A⁻¹) ^ 4 := mul_le_of_le_one_left (by positivity) (by norm_num)
      _ ≤ (3 * exp N) ^ 4 := pow_le_pow_left₀ (inv_pos.mpr hA).le hinv 4
      _ = _ := by rw [mul_pow, outer_exp_pow_four]; norm_num
  have hbR : bR ≤ 59049 * exp (F * N) := by
    have hI : (∫ x in morseRightTurn A B..morseRightCapEnd A B (1 / 100), -morseRho A B x) ≤ 59049 :=
      hright.2.trans (by simpa only [show (9 : ℝ) ^ 5 = 59049 by norm_num] using pow_le_pow_left₀ hA.le hA9 5)
    calc
      _ ≤ (j : ℝ) ^ 2 * 59049 := mul_le_mul_of_nonneg_left hI (sq_nonneg _)
      _ ≤ exp (F * N) * 59049 := mul_le_mul_of_nonneg_right hj2 (by norm_num)
      _ = _ := mul_comm _ _
  have hrightSize : 1 + aR + bR ≤ 60000 * exp ((F + 4) * N) := by
    have ha := haR.trans (mul_le_mul_of_nonneg_left hE4 (by norm_num : (0 : ℝ) ≤ 81))
    have hb := hbR.trans (mul_le_mul_of_nonneg_left hEF (by norm_num : (0 : ℝ) ≤ 59049))
    nlinarith only [ha, hb, hE]
  have hrightProd : aR * bR ≤ 1 * (j : ℝ) ^ 2 * A := by
    have hp := mul_le_mul_of_nonneg_left
      (morse_right_cap_balanced_product hB hAB hBA (by norm_num : (0 : ℝ) ≤ 1 / 100)) (sq_nonneg (j : ℝ))
    dsimp only [aR, bR]
    nlinarith only [hp, mul_nonneg (sq_nonneg (j : ℝ)) hA.le]
  have hrightFactor :
      morsePositiveEnergyFactor A B (j : ℝ) (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)) ≤
        exp ((4 * (60000 + (F + 4)) + 2) * N + 2 * tau) := by
    have hb₀ : 0 ≤ bR := mul_nonneg (sq_nonneg _) hright.1
    have hh := outer_positive_factor_le_exp hN (by norm_num : (0 : ℝ) ≤ 60000)
      (by norm_num : (0 : ℝ) ≤ 1) hA.le hj
      (by linarith only [haR₀, hb₀] : 0 ≤ 1 + aR + bR) hrightSize hrightProd
    simpa only [sqrt_one, mul_one, morsePositiveEnergyFactor, aR, bR, tau] using hh
  have hpeak : 0 ≤ A / 4 - B := by linarith only [hAB]
  have hpeak9 : A / 4 - B ≤ 9 := by linarith only [hA9, hB, hA]
  have hlog : log (1 + (j : ℝ) ^ 2 * (A / 4 - B)) ≤ (F + 10) * N := by
    have hq : 1 + (j : ℝ) ^ 2 * (A / 4 - B) ≤ 10 * exp (F * N) := by
      have hp := mul_le_mul_of_nonneg_left hpeak9 (sq_nonneg (j : ℝ))
      have hj' := mul_le_mul_of_nonneg_right hj2 (by norm_num : (0 : ℝ) ≤ 9)
      have he : 1 ≤ exp (F * N) := one_le_exp_iff.mpr (mul_nonneg hF hN₀)
      nlinarith only [hp, hj', he]
    have h10 : (10 : ℝ) ≤ exp (10 * N) :=
      (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 10) hN).trans
        ((le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _))
    have he : 1 + (j : ℝ) ^ 2 * (A / 4 - B) ≤ exp ((F + 10) * N) := by
      calc
        _ ≤ 10 * exp (F * N) := hq
        _ ≤ exp (10 * N) * exp (F * N) := mul_le_mul_of_nonneg_right h10 (exp_pos _).le
        _ = _ := by rw [← exp_add]; congr 1; ring
    simpa only [log_exp] using log_le_log (by positivity) he
  have hturn : morseRightTurn A B - morseLeftTurn A B ≤ 32 * N := by
    have hl : 0 ≤ morseLeftTurn A B := by
      exact neg_nonneg.mpr (log_nonpos
        (le_of_lt ((by norm_num : (0 : ℝ) < 1 / 2).trans (morseRootT_bounds hB hAB).2.2.1))
        (morseRootT_bounds hB hAB).2.2.2.le)
    have hr := (morseRightTurn_log_bounds hB hAB).2
    rw [log_div hB.ne' hA.ne', neg_sub, ← log_div hA.ne' hB.ne'] at hr
    have hratio : log (A / B) ≤ 32 * N := outer_morse_log_ratio_le hn hd
    linarith only [hl, hr, hratio]
  have hnegative : morseNegativeEnergyFactor A B (j : ℝ) ≤ exp ((2 * F + 52) * N) := by
    apply exp_le_exp.mpr
    change morseRightTurn A B - morseLeftTurn A B +
      2 * log (1 + (j : ℝ) ^ 2 * (A / 4 - B)) ≤ _
    nlinarith only [hturn, hlog]
  calc
    _ ≤ (exp ((4 * (60000 + (F + 4)) + 2) * N + 8 * tau) *
        exp ((2 * F + 52) * N)) *
        exp ((4 * (60000 + (F + 4)) + 2) * N + 2 * tau) :=
      mul_le_mul (mul_le_mul hleftFactor hnegative (exp_pos _).le (exp_pos _).le)
        hrightFactor (morsePositiveEnergyFactor_nonneg _ _ _ _ _) (by positivity)
    _ = exp ((10 * F + 480088) * N + 10 * tau) := by
      rw [← exp_add, ← exp_add]
      congr 1
      ring
    _ ≤ _ := exp_le_exp.mpr (by dsimp only [F, N, tau, A] at *; nlinarith only [hN₀])

end ContinuousFlexibility.Radial
