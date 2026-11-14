module

public import ContinuousFlexibility.Statements.RadialTargets
public import ContinuousFlexibility.Radial.MorseChainParameters

/-!
# Transition bands of the actual Morse scales

The least nonsquare choice determines the decreasing Morse parameters.
The frequency thresholds exhaust the frequencies, and a uniform estimate
controls every cell after a frequency's transition cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology

set_option backward.isDefEq.respectTransparency false

private theorem radialQ_log_ge_one (n : ℕ) : 1 ≤ log (exp 1 + (n : ℝ)) := by
  calc
    1 = log (exp 1) := (log_exp 1).symm
    _ ≤ _ := log_le_log (exp_pos _) (le_add_of_nonneg_right (Nat.cast_nonneg n))

theorem radialQ_strictMono : StrictMono Statements.radialQ := by
  intro n m hnm
  have hcast : (n : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hnm
  have hpow := rpow_lt_rpow (Nat.cast_nonneg (α := ℝ) n) hcast (by norm_num : (0 : ℝ) < 5 / 2)
  have hlog : log (exp 1 + (n : ℝ)) ≤ log (exp 1 + (m : ℝ)) :=
    log_le_log (add_pos_of_pos_of_nonneg (exp_pos _) (Nat.cast_nonneg n)) (add_le_add le_rfl hcast.le)
  unfold Statements.radialQ
  exact (mul_lt_mul_of_pos_right hpow (zero_lt_one.trans_le (radialQ_log_ge_one n))).trans_le
    (mul_le_mul_of_nonneg_left hlog (rpow_nonneg (Nat.cast_nonneg m) _))

theorem morseChainInteger_monotone : Monotone morseChainInteger := by
  intro n m hnm
  have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
  have hExp : exp ((n : ℝ) ^ 2) ≤ (morseChainInteger m : ℝ) :=
    (exp_le_exp.mpr (pow_le_pow_left₀ (Nat.cast_nonneg n) hcast 2)).trans (morseChainInteger_spec m).1
  exact le_of_not_gt (fun hlt =>
    (morseChainInteger_spec m).2 (morseChainInteger_minimal n (morseChainInteger m) hExp hlt))

private theorem morseTransition_A_pos (T : Statements.MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) : 0 < Statements.morseChainA T n :=
  (div_pos (exp_pos _) (by norm_num)).trans_le (morseChainA_exp_bounds T n hd).1

private theorem morseTransition_A_le (T : Statements.MorseChainData) {n m : ℕ}
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m) (hnm : n ≤ m) :
    Statements.morseChainA T m ≤ Statements.morseChainA T n := by
  have hdnPos : 0 < (T.d n : ℝ) := by
    rw [hdn]
    exact (exp_pos _).trans_le (morseChainInteger_spec n).1
  have hcast : (T.d n : ℝ) ≤ (T.d m : ℝ) := by
    rw [hdn, hdm]
    exact Nat.cast_le.mpr (morseChainInteger_monotone hnm)
  unfold Statements.morseChainA
  apply pow_le_pow_left₀ (by positivity) _ 2
  exact add_le_add (rpow_le_rpow_of_nonpos hdnPos hcast (by norm_num))
    (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hdnPos hcast (by norm_num)) (by norm_num))

theorem morseTransition_A_antitoneOn (T : Statements.MorseChainData)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    AntitoneOn (Statements.morseChainA T) (Ici T.index) := by
  intro n hn m hm hnm
  exact morseTransition_A_le T (hd n hn) (hd m hm) hnm

theorem morseTransition_threshold_eq_rpow (T : Statements.MorseChainData) (C : ℝ) (n : ℕ)
    (hd : T.d n = morseChainInteger n) :
    Statements.radialFrequencyThreshold T C n =
      C * Statements.radialQ n * (Statements.morseChainA T n) ^ (-1 / 2 : ℝ) := by
  unfold Statements.radialFrequencyThreshold
  rw [div_eq_mul_inv, sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    rpow_neg (morseTransition_A_pos T n hd).le]

private theorem morseTransition_threshold_lt (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    {n m : ℕ} (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m) (hnm : n < m) :
    Statements.radialFrequencyThreshold T C n < Statements.radialFrequencyThreshold T C m := by
  have hSn := sqrt_pos.mpr (morseTransition_A_pos T n hdn)
  have hSm := sqrt_pos.mpr (morseTransition_A_pos T m hdm)
  have hden := sqrt_le_sqrt (morseTransition_A_le T hdn hdm hnm.le)
  have hQm : 0 ≤ Statements.radialQ m := (sq_nonneg _).trans (radial_nat_sq_le_Q m)
  unfold Statements.radialFrequencyThreshold
  calc
    _ < C * Statements.radialQ m / sqrt (Statements.morseChainA T n) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (radialQ_strictMono hnm) hC) hSn
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hC.le hQm) hSm hden

theorem morseTransition_threshold_strictMonoOn (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    StrictMonoOn (Statements.radialFrequencyThreshold T C) (Ici T.index) := by
  intro n hn m hm hnm
  exact morseTransition_threshold_lt T hC (hd n hn) (hd m hm) hnm

theorem morseTransition_threshold_strictMono (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.d n = morseChainInteger n) : StrictMono (Statements.radialFrequencyThreshold T C) := by
  intro n m hnm
  exact morseTransition_threshold_lt T hC (hd n) (hd m) hnm

theorem morseTransition_threshold_tendsto (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    Tendsto (Statements.radialFrequencyThreshold T C) atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  obtain ⟨M, hM⟩ := exists_nat_ge (3 * b / C)
  filter_upwards [eventually_ge_atTop T.index, eventually_ge_atTop M, eventually_ge_atTop (1 : ℕ)]
    with n hn hMn hn1
  have hAn := morseChainA_exp_bounds T n (hd n hn)
  have hAn9 : Statements.morseChainA T n ≤ 9 := hAn.2.trans
    (mul_le_of_le_one_right (by norm_num) (exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))))
  have hroot : sqrt (Statements.morseChainA T n) ≤ 3 := by
    have h : sqrt (Statements.morseChainA T n) ≤ sqrt 9 := sqrt_le_sqrt hAn9
    rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num, sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)] at h
    exact h
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnQ : (n : ℝ) ≤ Statements.radialQ n := by
    have h := mul_nonneg (sub_nonneg.mpr hn1') (Nat.cast_nonneg (α := ℝ) n)
    exact (by nlinarith only [h] : (n : ℝ) ≤ (n : ℝ) ^ 2).trans (radial_nat_sq_le_Q n)
  have hb : 3 * b ≤ C * (n : ℝ) := by
    have h := (div_le_iff₀ hC).mp (hM.trans (Nat.cast_le.mpr hMn))
    exact h.trans_eq (mul_comm _ _)
  calc
    _ ≤ C * (n : ℝ) / 3 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr (by linarith only [hb])
    _ ≤ C * Statements.radialQ n / 3 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnQ hC.le) (by norm_num)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hC.le ((sq_nonneg _).trans (radial_nat_sq_le_Q n)))
      (sqrt_pos.mpr (morseTransition_A_pos T n (hd n hn))) hroot

theorem morseTransition_initial_band_iff (T : Statements.MorseChainData) (C : ℝ) (j : ℕ) :
    Statements.radialFrequencyBand T C T.index j ↔
      2 ≤ j ∧ (j : ℝ) < Statements.radialFrequencyThreshold T C T.index := by
  unfold Statements.radialFrequencyBand
  rw [ite_eq_left rfl]
  constructor
  · rintro ⟨_, hj, hhi⟩
    exact ⟨by exact_mod_cast hj, hhi⟩
  · rintro ⟨hj, hhi⟩
    exact ⟨le_rfl, by exact_mod_cast hj, hhi⟩

/-- Every integer frequency from two onward is in exactly one public band. -/
theorem morseTransition_existsUnique_band (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) {j : ℕ} (hj : 2 ≤ j) :
    ∃! n : ℕ, Statements.radialFrequencyBand T C n j := by
  have hlim := morseTransition_threshold_tendsto T hC hd
  have hex : ∃ n : ℕ, T.index ≤ n ∧ (j : ℝ) < Statements.radialFrequencyThreshold T C n :=
    ((eventually_ge_atTop T.index).and (hlim.eventually (eventually_gt_atTop (j : ℝ)))).exists
  classical
  let n := Nat.find hex
  have hn : T.index ≤ n ∧ (j : ℝ) < Statements.radialFrequencyThreshold T C n := Nat.find_spec hex
  have hband : Statements.radialFrequencyBand T C n j := by
    refine ⟨hn.1, ?_, hn.2⟩
    split_ifs with heq
    · exact_mod_cast hj
    · have hprev : n - 1 < n := by omega
      have hidx : T.index ≤ n - 1 := by omega
      exact le_of_not_gt (fun h => Nat.find_min hex hprev ⟨hidx, h⟩)
  have hMono := morseTransition_threshold_strictMonoOn T hC hd
  have hnot (m k : ℕ) (hm : Statements.radialFrequencyBand T C m j)
      (hk : Statements.radialFrequencyBand T C k j) (hmk : m < k) : False := by
    have hkN : k ≠ T.index := by have := hm.1; omega
    have hprev : m ≤ k - 1 := by omega
    have hidx : T.index ≤ k - 1 := hm.1.trans hprev
    have hle := hMono.monotoneOn hm.1 hidx hprev
    have hlo := hk.2.1
    rw [ite_eq_right hkN] at hlo
    exact (not_lt_of_ge (hle.trans hlo)) hm.2.2
  refine ⟨n, hband, ?_⟩
  intro m hm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hnot m n hm hband hlt
  · exact hnot n m hband hm hgt

theorem morseTransition_earlier_cap_action (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) {n j m : ℕ}
    (hband : Statements.radialFrequencyBand T C n j) (hm : T.index ≤ m) (hmn : m < n) :
    C * Statements.radialQ m ≤ (j : ℝ) * sqrt (Statements.morseChainA T m) := by
  have hn : n ≠ T.index := by omega
  have hmPrev : m ≤ n - 1 := by omega
  have hlo := hband.2.1
  rw [ite_eq_right hn] at hlo
  have hMono := morseTransition_threshold_strictMonoOn T hC hd
  have ht : Statements.radialFrequencyThreshold T C m ≤ (j : ℝ) :=
    (hMono.monotoneOn hm (hm.trans hmPrev) hmPrev).trans hlo
  exact (div_le_iff₀ (sqrt_pos.mpr (morseTransition_A_pos T m (hd m hm)))).mp ht

/-- The retained Morse parameters have a fixed positive logarithmic gap. -/
theorem morseTransition_log_ratio_lower (T : Statements.MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) :
    log 4 ≤ log (Statements.morseChainA T n / Statements.morseChainB T n) := by
  have hd2 : (2 : ℝ) ≤ T.d n := by
    rw [hd]
    exact_mod_cast morseChainInteger_ge_two n
  have hpar := morseChainParameters_pos T n hd2
  exact log_le_log (by norm_num : (0 : ℝ) < 4)
    ((le_div_iff₀ hpar.2).mpr hpar.1.le)

private theorem morseTransition_sqrt_log_ratio_le (T : Statements.MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) :
    sqrt (log (Statements.morseChainA T n / Statements.morseChainB T n)) ≤ 5 * ((n : ℝ) + 1) := by
  let d : ℝ := T.d n
  let A := Statements.morseChainA T n
  let B := Statements.morseChainB T n
  have hd2 : 2 ≤ d := by
    change (2 : ℝ) ≤ (T.d n : ℝ)
    rw [hd]
    exact_mod_cast morseChainInteger_ge_two n
  have hd1 : 1 ≤ d := (by norm_num : (1 : ℝ) ≤ 2).trans hd2
  have hd0 : 0 < d := zero_lt_one.trans_le hd1
  have hA : 0 < A := morseTransition_A_pos T n hd
  have hB : 0 < B := (morseChainParameters_pos T n hd2).2
  have hBp : B = (d ^ 9)⁻¹ := by
    change Statements.morseChainB T n = _
    rw [morseChainB_inv_pow T n hd0.le, inv_pow]
  have hratio : A / B ≤ 9 * d ^ 8 := by
    rw [hBp, div_inv_eq_mul]
    calc
      _ ≤ (9 * d⁻¹) * d ^ 9 := mul_le_mul_of_nonneg_right (morseChainA_inv_bounds T n hd1).2
        (pow_nonneg hd0.le _)
      _ = (9 * (d⁻¹ * d)) * d ^ 8 := by ring
      _ = _ := by rw [inv_mul_cancel₀ hd0.ne', mul_one]
  have hlog := log_le_log (div_pos hA hB) hratio
  rw [log_mul (by norm_num : (9 : ℝ) ≠ 0) (pow_ne_zero 8 hd0.ne'), log_pow] at hlog
  have hdU : d ≤ 3 * exp ((n : ℝ) ^ 2) := by
    calc
      _ = (morseChainInteger n : ℝ) := by dsimp [d]; rw [hd]
      _ ≤ exp ((n : ℝ) ^ 2) + 2 := (morseChainInteger_lt n).le
      _ ≤ _ := by linarith only [one_le_exp_iff.mpr (sq_nonneg (n : ℝ))]
  have hdLog := log_le_log hd0 hdU
  rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (exp_ne_zero _), log_exp] at hdLog
  have hlog3 : log (3 : ℝ) ≤ 2 := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  have hlog9 : log (9 : ℝ) ≤ 8 := by
    simpa only [show (9 : ℝ) - 1 = 8 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
  have hupper : log (A / B) ≤ (5 * ((n : ℝ) + 1)) ^ 2 := by
    nlinarith only [hlog, hdLog, hlog3, hlog9, Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]
  exact (sqrt_le_sqrt hupper).trans_eq (sqrt_sq (by positivity))

private theorem morseTransition_A_ratio_le (T : Statements.MorseChainData) (n m : ℕ)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m) :
    Statements.morseChainA T m / Statements.morseChainA T n ≤
      27 * exp ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) := by
  have hAn := (morseChainA_exp_bounds T n hdn).1
  have hAm := (morseChainA_exp_bounds T m hdm).2
  calc
    _ ≤ (9 * exp (-(m : ℝ) ^ 2)) / Statements.morseChainA T n :=
      div_le_div_of_nonneg_right hAm (morseTransition_A_pos T n hdn).le
    _ ≤ (9 * exp (-(m : ℝ) ^ 2)) / (exp (-(n : ℝ) ^ 2) / 3) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos (exp_pos _) (by norm_num)) hAn
    _ = 27 * (exp (-(m : ℝ) ^ 2) / exp (-(n : ℝ) ^ 2)) := by
      rw [div_div_eq_mul_div]
      ring
    _ = _ := by
      rw [← exp_sub]
      congr 2
      ring

private theorem morseTransition_deep_ratio_bound (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) {n j m : ℕ}
    (hn : T.index ≤ n) (hupper : (j : ℝ) < Statements.radialFrequencyThreshold T C n)
    (hm : n < m) :
    (j : ℝ) ^ 2 * Statements.morseChainA T m *
        sqrt (log (Statements.morseChainA T m / Statements.morseChainB T m)) ≤
      5 * C ^ 2 * Statements.radialQ n ^ 2 * (Statements.morseChainA T m / Statements.morseChainA T n) *
        ((m : ℝ) + 1) := by
  let A := Statements.morseChainA T
  let B := Statements.morseChainB T
  have hAn := morseTransition_A_pos T n (hd n hn)
  have hAm := morseTransition_A_pos T m (hd m (hn.trans hm.le))
  have hQ : 0 ≤ Statements.radialQ n := (sq_nonneg _).trans (radial_nat_sq_le_Q n)
  have hj : (j : ℝ) ^ 2 ≤ (C * Statements.radialQ n) ^ 2 / A n := by
    have hjlt : (j : ℝ) < C * Statements.radialQ n / sqrt (A n) := hupper
    have h := (sq_le_sq₀ (Nat.cast_nonneg (α := ℝ) j)
      (div_nonneg (mul_nonneg hC.le hQ) (sqrt_nonneg _))).2 hjlt.le
    rwa [div_pow, sq_sqrt hAn.le] at h
  have hL := morseTransition_sqrt_log_ratio_le T m (hd m (hn.trans hm.le))
  calc
    _ ≤ ((C * Statements.radialQ n) ^ 2 / A n) * A m * sqrt (log (A m / B m)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj hAm.le) (sqrt_nonneg _)
    _ ≤ ((C * Statements.radialQ n) ^ 2 / A n) * A m * (5 * ((m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hL (mul_nonneg (div_nonneg (sq_nonneg _) hAn.le) hAm.le)
    _ = _ := by dsimp [A]; ring

/-- The explicit neighboring-cell estimate of §5, with a constant independent
of the frequency and the transition index. -/
theorem morseTransition_next_deep_bound (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) {n j : ℕ}
    (hband : Statements.radialFrequencyBand T C n j) :
    (j : ℝ) ^ 2 * Statements.morseChainA T (n + 1) *
        sqrt (log (Statements.morseChainA T (n + 1) / Statements.morseChainB T (n + 1))) ≤
      10 * C ^ 2 * Statements.radialQ n ^ 2 *
        (Statements.morseChainA T (n + 1) / Statements.morseChainA T n) * ((n : ℝ) + 1) := by
  have hn : n < n + 1 := Nat.lt_succ_self n
  have hAn := morseTransition_A_pos T n (hd n hband.1)
  have hAs := morseTransition_A_pos T (n + 1) (hd (n + 1) (hband.1.trans hn.le))
  have hcoef : 0 ≤ 5 * C ^ 2 * Statements.radialQ n ^ 2 *
      (Statements.morseChainA T (n + 1) / Statements.morseChainA T n) := by positivity
  refine (morseTransition_deep_ratio_bound T hC hd hband.1 hband.2.2 hn).trans ?_
  push_cast
  calc
    _ ≤ 5 * C ^ 2 * Statements.radialQ n ^ 2 *
        (Statements.morseChainA T (n + 1) / Statements.morseChainA T n) * (2 * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith only [Nat.cast_nonneg (α := ℝ) n]) hcoef
    _ = _ := by ring

private theorem morseTransition_deeper_exp_bound {n m : ℕ} (hnm : n < m) :
    ((m : ℝ) + 1) * exp ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) ≤ exp (-(n : ℝ)) := by
  have hm : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hnm
  have hp : 0 ≤ ((m : ℝ) - (n : ℝ) - 1) * ((m : ℝ) + (n : ℝ)) :=
    mul_nonneg (by linarith only [hm]) (by positivity)
  calc
    _ ≤ exp (m : ℝ) * exp ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (add_one_le_exp _) (exp_pos _).le
    _ = exp ((n : ℝ) ^ 2 - (m : ℝ) ^ 2 + (m : ℝ)) := by rw [← exp_add]; congr 1; ring
    _ ≤ _ := exp_le_exp.mpr (by nlinarith only [hp])

/-- Every frequency below the cutoff has the same bound on all deeper cells.
No lower endpoint of a transition band is needed. -/
theorem morseTransition_deeper_bound_of_upper (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) {n j m : ℕ}
    (hn : T.index ≤ n) (hupper : (j : ℝ) < Statements.radialFrequencyThreshold T C n)
    (hm : n < m) :
    (j : ℝ) ^ 2 * Statements.morseChainA T m *
        sqrt (log (Statements.morseChainA T m / Statements.morseChainB T m)) ≤
      135 * C ^ 2 * Statements.radialQ n ^ 2 * exp (-(n : ℝ)) := by
  have hratio := morseTransition_A_ratio_le T n m (hd n hn) (hd m (hn.trans hm.le))
  refine (morseTransition_deep_ratio_bound T hC hd hn hupper hm).trans ?_
  calc
    _ ≤ 5 * C ^ 2 * Statements.radialQ n ^ 2 *
        (27 * exp ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (by positivity)) (by positivity)
    _ = 135 * C ^ 2 * Statements.radialQ n ^ 2 *
        (((m : ℝ) + 1) * exp ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (morseTransition_deeper_exp_bound hm) (by positivity)

/-- The original transition-band estimate is the upper-cutoff estimate. -/
theorem morseTransition_deeper_bound (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) {n j m : ℕ}
    (hband : Statements.radialFrequencyBand T C n j) (hm : n < m) :
    (j : ℝ) ^ 2 * Statements.morseChainA T m *
        sqrt (log (Statements.morseChainA T m / Statements.morseChainB T m)) ≤
      135 * C ^ 2 * Statements.radialQ n ^ 2 * exp (-(n : ℝ)) :=
  morseTransition_deeper_bound_of_upper T hC hd hband.1 hband.2.2 hm

private theorem morseTransition_q_polynomial_bound (n : ℕ) :
    Statements.radialQ n ≤ (exp 1 + 1) * ((n : ℝ) + 1) ^ 4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h₁ : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith only [hn]
  have hpow : (n : ℝ) ^ (5 / 2 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by
    calc
      _ ≤ ((n : ℝ) + 1) ^ (5 / 2 : ℝ) := rpow_le_rpow hn (by linarith) (by norm_num)
      _ ≤ ((n : ℝ) + 1) ^ (3 : ℝ) := rpow_le_rpow_of_exponent_le h₁ (by norm_num)
      _ = _ := rpow_natCast _ 3
  have hlog : log (exp 1 + (n : ℝ)) ≤ (exp 1 + 1) * ((n : ℝ) + 1) := by
    refine (log_le_self (by positivity)).trans ?_
    nlinarith only [hn, mul_nonneg (exp_pos (1 : ℝ)).le hn]
  unfold Statements.radialQ
  calc
    _ ≤ ((n : ℝ) + 1) ^ 3 * ((exp 1 + 1) * ((n : ℝ) + 1)) :=
      mul_le_mul hpow hlog (zero_le_one.trans (radialQ_log_ge_one n)) (by positivity)
    _ = _ := by ring

theorem morseTransition_deeper_bound_tendsto (C : ℝ) :
    Tendsto (fun n : ℕ => 135 * C ^ 2 * Statements.radialQ n ^ 2 * exp (-(n : ℝ))) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 8 * exp (-((n : ℝ) + 1))) atTop (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 8).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  let K := 135 * C ^ 2 * (exp 1 + 1) ^ 2 * exp 1
  have hlim : Tendsto (fun n : ℕ => K * (((n : ℝ) + 1) ^ 8 * exp (-((n : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul K
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  have hsq := (sq_le_sq₀ ((sq_nonneg _).trans (radial_nat_sq_le_Q n)) (by positivity)).2
    (morseTransition_q_polynomial_bound n)
  calc
    _ ≤ 135 * C ^ 2 * ((exp 1 + 1) * ((n : ℝ) + 1) ^ 4) ^ 2 * exp (-(n : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (exp_pos _).le
    _ = _ := by
      rw [show exp (-(n : ℝ)) = exp 1 * exp (-((n : ℝ) + 1)) by rw [← exp_add]; congr 1; ring]
      dsimp [K]
      ring

/-- The coefficient on the right side of the neighboring-cell bound in
`eq:rad-eq-rm22` itself tends to zero. -/
theorem morseTransition_next_ratio_tendsto (T : Statements.MorseChainData)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    Tendsto (fun n : ℕ => Statements.radialQ n ^ 2 *
      (Statements.morseChainA T (n + 1) / Statements.morseChainA T n) * ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 135 * Statements.radialQ n ^ 2 * exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [one_pow, mul_one] using morseTransition_deeper_bound_tendsto (1 : ℝ)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop T.index] with n hn
    have hAn := morseTransition_A_pos T n (hd n hn)
    have hAs := morseTransition_A_pos T (n + 1) (hd (n + 1) (hn.trans (Nat.le_succ n)))
    positivity
  · filter_upwards [eventually_ge_atTop T.index] with n hn
    have hratio := morseTransition_A_ratio_le T n (n + 1) (hd n hn)
      (hd (n + 1) (hn.trans (Nat.le_succ n)))
    have hscale : ((n : ℝ) + 1) * exp ((n : ℝ) ^ 2 - ((n + 1 : ℕ) : ℝ) ^ 2) ≤ exp (-(n : ℝ)) := by
      calc
        _ ≤ (((n + 1 : ℕ) : ℝ) + 1) * exp ((n : ℝ) ^ 2 - ((n + 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by push_cast; linarith) (exp_pos _).le
        _ ≤ _ := morseTransition_deeper_exp_bound (Nat.lt_succ_self n)
    calc
      _ ≤ Statements.radialQ n ^ 2 * (27 * exp ((n : ℝ) ^ 2 - ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (sq_nonneg _)) (by positivity)
      _ = 27 * Statements.radialQ n ^ 2 *
          (((n : ℝ) + 1) * exp ((n : ℝ) ^ 2 - ((n + 1 : ℕ) : ℝ) ^ 2)) := by ring
      _ ≤ 27 * Statements.radialQ n ^ 2 * exp (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ ≤ _ := by
        have h := mul_nonneg (sq_nonneg (Statements.radialQ n)) (exp_pos (-(n : ℝ))).le
        nlinarith only [h]

/-- A single sufficiently deep cutoff controls every frequency below it,
including frequencies below the lower endpoint of its old transition band. -/
theorem morseTransition_eventually_deep_of_upper (T : Statements.MorseChainData)
    {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, T.index ≤ n →
      (j : ℝ) < Statements.radialFrequencyThreshold T C n → ∀ m, n < m →
        (j : ℝ) ^ 2 * Statements.morseChainA T m *
          sqrt (log (Statements.morseChainA T m / Statements.morseChainB T m)) < ε := by
  filter_upwards [(morseTransition_deeper_bound_tendsto C).eventually (eventually_lt_nhds hε)]
    with n hn
  intro j hidx hj m hm
  exact (morseTransition_deeper_bound_of_upper T hC hd hidx hj hm).trans_lt hn

theorem morseTransition_eventually_deep (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j, Statements.radialFrequencyBand T C n j → ∀ m, n < m →
      (j : ℝ) ^ 2 * Statements.morseChainA T m *
        sqrt (log (Statements.morseChainA T m / Statements.morseChainB T m)) < ε := by
  filter_upwards [morseTransition_eventually_deep_of_upper T hC hd hε]
    with n hn
  intro j hj m hm
  exact hn j hj.1 hj.2.2 m hm

end ContinuousFlexibility.Radial
