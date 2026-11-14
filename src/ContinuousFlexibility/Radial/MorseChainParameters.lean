module

public import ContinuousFlexibility.Radial.MorseChainScales

/-!
# The actual parameters and turning points of the Morse cells

These are the parameters from the least nonsquare choices in Section 5.
The estimates apply to the actual definitions in `Statements.Radial`.
No radius solution, positivity of its derivative, or gluing is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem morseChainA_factor (T : Statements.MorseChainData) (n : ℕ)
    (hd : 0 < (T.d n : ℝ)) :
    Statements.morseChainA T n = (T.d n : ℝ)⁻¹ *
      (1 + 2 * (((T.d n : ℝ) ^ 4)⁻¹)) ^ 2 := by
  let d : ℝ := T.d n
  have hp : 0 < d := hd
  have h4 : d ^ (-4 : ℝ) = (d ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hp.le, Real.rpow_natCast]
  have hm : d ^ (-1 / 2 : ℝ) * (d ^ 4)⁻¹ = d ^ (-9 / 2 : ℝ) := by
    rw [← h4, ← Real.rpow_add hp,
      show (-1 / 2 : ℝ) + (-4) = -9 / 2 by norm_num]
  have hsq : (d ^ (-1 / 2 : ℝ)) ^ 2 = d⁻¹ := by
    rw [pow_two, ← Real.rpow_add hp,
      show (-1 / 2 : ℝ) + (-1 / 2) = -1 by norm_num,
      Real.rpow_neg hp.le, Real.rpow_one]
  change (d ^ (-1 / 2 : ℝ) + 2 * d ^ (-9 / 2 : ℝ)) ^ 2 =
    d⁻¹ * (1 + 2 * (d ^ 4)⁻¹) ^ 2
  calc
    _ = (d ^ (-1 / 2 : ℝ) * (1 + 2 * (d ^ 4)⁻¹)) ^ 2 := by rw [← hm]; ring
    _ = _ := by rw [mul_pow, hsq]

theorem morseChainB_inv_pow (T : Statements.MorseChainData) (n : ℕ)
    (hd : 0 ≤ (T.d n : ℝ)) :
    Statements.morseChainB T n = ((T.d n : ℝ)⁻¹) ^ 9 := by
  unfold Statements.morseChainB
  rw [show (-9 : ℝ) = -((9 : ℕ) : ℝ) by norm_num, Real.rpow_neg hd,
    Real.rpow_natCast, inv_pow]

theorem morseChainA_inv_bounds (T : Statements.MorseChainData) (n : ℕ)
    (hd : 1 ≤ (T.d n : ℝ)) :
    (T.d n : ℝ)⁻¹ ≤ Statements.morseChainA T n ∧
      Statements.morseChainA T n ≤ 9 * (T.d n : ℝ)⁻¹ := by
  let d : ℝ := T.d n
  have hd1 : 1 ≤ d := hd
  have hp : 0 < d := zero_lt_one.trans_le hd1
  have hpow : 1 ≤ d ^ 4 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd1 4
  have h0 : 0 ≤ (d ^ 4)⁻¹ := inv_nonneg.mpr (pow_nonneg hp.le _)
  have h1 : (d ^ 4)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hpow
  have hlow : 1 ≤ 1 + 2 * (d ^ 4)⁻¹ := by linarith
  have hhigh : 1 + 2 * (d ^ 4)⁻¹ ≤ 3 := by linarith
  have hsqlo : 1 ≤ (1 + 2 * (d ^ 4)⁻¹) ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hlow 2
  have hsqhi : (1 + 2 * (d ^ 4)⁻¹) ^ 2 ≤ 9 := by
    calc
      _ ≤ (3 : ℝ) ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hlow) hhigh 2
      _ = 9 := by norm_num
  rw [morseChainA_factor T n hp]
  change d⁻¹ ≤ d⁻¹ * (1 + 2 * (d ^ 4)⁻¹) ^ 2 ∧
    d⁻¹ * (1 + 2 * (d ^ 4)⁻¹) ^ 2 ≤ 9 * d⁻¹
  refine ⟨?_, ?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqlo (inv_nonneg.mpr hp.le)
  · exact (mul_le_mul_of_nonneg_left hsqhi (inv_nonneg.mpr hp.le)).trans_eq (mul_comm _ _)

theorem morseChainB_A_bounds (T : Statements.MorseChainData) (n : ℕ)
    (hd : 1 ≤ (T.d n : ℝ)) :
    Statements.morseChainA T n ^ 9 / (9 : ℝ) ^ 9 ≤ Statements.morseChainB T n ∧
      Statements.morseChainB T n ≤ Statements.morseChainA T n ^ 9 := by
  have hp : 0 < (T.d n : ℝ) := zero_lt_one.trans_le hd
  have hi := inv_nonneg.mpr hp.le
  have hA := morseChainA_inv_bounds T n hd
  rw [morseChainB_inv_pow T n hp.le]
  refine ⟨?_, pow_le_pow_left₀ hi hA.1 9⟩
  apply (div_le_iff₀ (by positivity : 0 < (9 : ℝ) ^ 9)).mpr
  calc
    _ ≤ (9 * (T.d n : ℝ)⁻¹) ^ 9 := pow_le_pow_left₀ (hi.trans hA.1) hA.2 9
    _ = _ := by rw [mul_pow, mul_comm]

theorem morseChainParameters_pos (T : Statements.MorseChainData) (n : ℕ)
    (hd : 2 ≤ (T.d n : ℝ)) :
    4 * Statements.morseChainB T n < Statements.morseChainA T n ∧
      0 < Statements.morseChainB T n := by
  have hd1 : 1 ≤ (T.d n : ℝ) := (by norm_num : (1 : ℝ) ≤ 2).trans hd
  have hp := zero_lt_one.trans_le hd1
  have hi := inv_pos.mpr hp
  have hhalf : (T.d n : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd
  have h8 := pow_le_pow_left₀ hi.le hhalf 8
  rw [morseChainB_inv_pow T n hp.le]
  refine ⟨?_, pow_pos hi 9⟩
  calc
    _ = (T.d n : ℝ)⁻¹ * (4 * ((T.d n : ℝ)⁻¹) ^ 8) := by rw [pow_succ]; ring
    _ ≤ (T.d n : ℝ)⁻¹ * (4 * (1 / 2 : ℝ) ^ 8) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h8 (by norm_num)) hi.le
    _ < (T.d n : ℝ)⁻¹ * 1 := mul_lt_mul_of_pos_left (by norm_num) hi
    _ = (T.d n : ℝ)⁻¹ := mul_one _
    _ ≤ _ := (morseChainA_inv_bounds T n hd1).1

theorem morseChainA_exp_bounds (T : Statements.MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) :
    exp (-(n : ℝ) ^ 2) / 3 ≤ Statements.morseChainA T n ∧
      Statements.morseChainA T n ≤ 9 * exp (-(n : ℝ) ^ 2) := by
  let E : ℝ := exp ((n : ℝ) ^ 2)
  have hE1 : 1 ≤ E := one_le_exp_iff.mpr (sq_nonneg _)
  have hEp : 0 < E := zero_lt_one.trans_le hE1
  have hL : E ≤ (T.d n : ℝ) := by rw [hd]; exact (morseChainInteger_spec n).1
  have hU : (T.d n : ℝ) ≤ 3 * E := by
    rw [hd]
    have hh : (morseChainInteger n : ℝ) < E + 2 := morseChainInteger_lt n
    linarith
  have hp : 0 < (T.d n : ℝ) := hEp.trans_le hL
  have hA := morseChainA_inv_bounds T n (hE1.trans hL)
  have hinvlo : (3 * E)⁻¹ ≤ (T.d n : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hp hU
  have hinvhi : (T.d n : ℝ)⁻¹ ≤ E⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hEp hL
  have he : exp (-(n : ℝ) ^ 2) = E⁻¹ := exp_neg _
  refine ⟨?_, ?_⟩
  · rw [he]
    calc
      E⁻¹ / 3 = (3 * E)⁻¹ := by rw [mul_inv_rev, div_eq_mul_inv]
      _ ≤ (T.d n : ℝ)⁻¹ := hinvlo
      _ ≤ _ := hA.1
  · rw [he]
    exact hA.2.trans (mul_le_mul_of_nonneg_left hinvhi (by norm_num))

theorem morseChainA_le_of_sq_ge_log (T : Statements.MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) {ε : ℝ} (hε : 0 < ε)
    (hn : log (9 / ε) ≤ (n : ℝ) ^ 2) : Statements.morseChainA T n ≤ ε := by
  calc
    _ ≤ 9 * exp (-(n : ℝ) ^ 2) := (morseChainA_exp_bounds T n hd).2
    _ ≤ 9 * exp (-log (9 / ε)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hn)) (by norm_num)
    _ = ε := by
      rw [exp_neg, exp_log (div_pos (by norm_num) hε), inv_div]
      ring

/-- The small root in `t = exp(-X)` gives the right turning point in `X`. -/
def morseRightRootT (A B : ℝ) : ℝ := (1 - sqrt (1 - 4 * B / A)) / 2

def morseLeftRootT (A B : ℝ) : ℝ := (1 + sqrt (1 - 4 * B / A)) / 2

def morseRightTurn (A B : ℝ) : ℝ := -log (morseRightRootT A B)

def morseLeftTurn (A B : ℝ) : ℝ := -log (morseLeftRootT A B)

private theorem morse_discriminant_pos {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    0 < 1 - 4 * B / A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  apply sub_pos.mpr
  apply (div_lt_iff₀ hA).mpr
  simpa only [one_mul] using hAB

theorem morseRootT_bounds {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    0 < morseRightRootT A B ∧ morseRightRootT A B < 1 / 2 ∧
      1 / 2 < morseLeftRootT A B ∧ morseLeftRootT A B < 1 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hδ := morse_discriminant_pos hB hAB
  have hδ1 : 1 - 4 * B / A < 1 := sub_lt_self _ (div_pos (mul_pos (by norm_num) hB) hA)
  have hs0 := sqrt_pos.mpr hδ
  have hs1 : sqrt (1 - 4 * B / A) < 1 := by
    simpa only [sqrt_one] using sqrt_lt_sqrt hδ.le hδ1
  unfold morseRightRootT morseLeftRootT
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem morseRootT_sum (A B : ℝ) : morseRightRootT A B + morseLeftRootT A B = 1 := by
  unfold morseRightRootT morseLeftRootT
  ring

theorem morseRootT_mul {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    morseRightRootT A B * morseLeftRootT A B = B / A := by
  have hsq := sq_sqrt (morse_discriminant_pos hB hAB).le
  unfold morseRightRootT morseLeftRootT
  calc
    _ = (1 - sqrt (1 - 4 * B / A) ^ 2) / 4 := by ring
    _ = _ := by rw [hsq]; ring

theorem morseRightRootT_ratio_bounds {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    B / A ≤ morseRightRootT A B ∧ morseRightRootT A B ≤ 2 * (B / A) := by
  obtain ⟨hR, _, hLlo, hLhi⟩ := morseRootT_bounds hB hAB
  have hprod := morseRootT_mul hB hAB
  constructor
  · rw [← hprod]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hLhi.le hR.le
  · have h := mul_le_mul_of_nonneg_left hLlo.le hR.le
    rw [hprod] at h
    linarith

theorem morseRightTurn_log_bounds {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    -log (2 * (B / A)) ≤ morseRightTurn A B ∧
      morseRightTurn A B ≤ -log (B / A) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hb := morseRightRootT_ratio_bounds hB hAB
  refine ⟨?_, ?_⟩
  · exact neg_le_neg (log_le_log (morseRootT_bounds hB hAB).1 hb.2)
  · exact neg_le_neg (log_le_log (div_pos hB hA) hb.1)

theorem morseTurn_order {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    morseLeftTurn A B < morseRightTurn A B := by
  obtain ⟨hR, hRhi, hLlo, _⟩ := morseRootT_bounds hB hAB
  exact neg_lt_neg (log_lt_log hR (hRhi.trans hLlo))

theorem exp_neg_morseLeftTurn {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    exp (-morseLeftTurn A B) = morseLeftRootT A B := by
  have hL : 0 < morseLeftRootT A B := (by norm_num : (0 : ℝ) < 1 / 2).trans
    (morseRootT_bounds hB hAB).2.2.1
  rw [morseLeftTurn, neg_neg, exp_log hL]

theorem exp_neg_morseRightTurn {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    exp (-morseRightTurn A B) = morseRightRootT A B := by
  rw [morseRightTurn, neg_neg, exp_log (morseRootT_bounds hB hAB).1]

private theorem morse_exp_two (x : ℝ) : exp (-2 * x) = exp (-x) ^ 2 := by
  rw [pow_two, ← exp_add]
  congr 1
  ring

theorem morseRho_factor {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) (x : ℝ) :
    morseRho A B x = A * (exp (-x) - morseRightRootT A B) *
      (morseLeftRootT A B - exp (-x)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hcancel : A * (B / A) = B := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hA.ne']
  unfold morseRho
  rw [morse_exp_two]
  calc
    _ = A * ((morseRightRootT A B + morseLeftRootT A B) * exp (-x) -
        exp (-x) ^ 2 - morseRightRootT A B * morseLeftRootT A B) := by
      simp only [morseRootT_sum, morseRootT_mul hB hAB, one_mul, mul_sub, hcancel]
    _ = _ := by ring

theorem morseRho_zero_iff_turn {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) (x : ℝ) :
    morseRho A B x = 0 ↔ x = morseLeftTurn A B ∨ x = morseRightTurn A B := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  rw [morseRho_factor hB hAB]
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with h | h
    · have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hA.ne')
      right
      rw [morseRightTurn, ← he, log_exp, neg_neg]
    · have he := sub_eq_zero.mp h
      left
      rw [morseLeftTurn, he, log_exp, neg_neg]
  · rintro (rfl | rfl)
    · simp only [exp_neg_morseLeftTurn hB hAB, sub_self, mul_zero]
    · simp only [exp_neg_morseRightTurn hB hAB, sub_self, mul_zero, zero_mul]

theorem morseRho_pos_between_turns {A B x : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hx : x ∈ Ioo (morseLeftTurn A B) (morseRightTurn A B)) : 0 < morseRho A B x := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hR : morseRightRootT A B < exp (-x) := by
    rw [← exp_neg_morseRightTurn hB hAB]
    exact exp_lt_exp.mpr (neg_lt_neg hx.2)
  have hL : exp (-x) < morseLeftRootT A B := by
    rw [← exp_neg_morseLeftTurn hB hAB]
    exact exp_lt_exp.mpr (neg_lt_neg hx.1)
  rw [morseRho_factor hB hAB]
  exact mul_pos (mul_pos hA (sub_pos.mpr hR)) (sub_pos.mpr hL)

theorem morseRho_neg_before_left_turn {A B x : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hx : x < morseLeftTurn A B) : morseRho A B x < 0 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hb := morseRootT_bounds hB hAB
  have hL : morseLeftRootT A B < exp (-x) := by
    rw [← exp_neg_morseLeftTurn hB hAB]
    exact exp_lt_exp.mpr (neg_lt_neg hx)
  rw [morseRho_factor hB hAB]
  exact mul_neg_of_pos_of_neg
    (mul_pos hA (sub_pos.mpr (hb.2.1.trans (hb.2.2.1.trans hL)))) (sub_neg.mpr hL)

theorem morseRho_neg_after_right_turn {A B x : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hx : morseRightTurn A B < x) : morseRho A B x < 0 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hb := morseRootT_bounds hB hAB
  have hR : exp (-x) < morseRightRootT A B := by
    rw [← exp_neg_morseRightTurn hB hAB]
    exact exp_lt_exp.mpr (neg_lt_neg hx)
  rw [morseRho_factor hB hAB]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hA (sub_neg.mpr hR))
    (sub_pos.mpr (hR.trans (hb.2.1.trans hb.2.2.1)))

theorem morseRho_right_cap_bounds {A B x : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hx : morseRightTurn A B ≤ x) : 0 ≤ -morseRho A B x ∧ -morseRho A B x ≤ B := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hnonpos : morseRho A B x ≤ 0 := by
    rcases eq_or_lt_of_le hx with h | h
    · exact le_of_eq ((morseRho_zero_iff_turn hB hAB x).mpr (Or.inr h.symm))
    · exact (morseRho_neg_after_right_turn hB hAB h).le
  have ht : exp (-x) ≤ morseRightRootT A B := by
    rw [← exp_neg_morseRightTurn hB hAB]
    exact exp_le_exp.mpr (neg_le_neg hx)
  have ht1 : exp (-x) ≤ 1 :=
    ht.trans ((morseRootT_bounds hB hAB).2.1.le.trans (by norm_num))
  have hterm : 0 ≤ exp (-x) - exp (-x) ^ 2 := by
    nlinarith only [mul_nonneg (exp_pos (-x)).le (sub_nonneg.mpr ht1)]
  refine ⟨neg_nonneg.mpr hnonpos, ?_⟩
  unfold morseRho
  rw [morse_exp_two]
  linarith only [mul_nonneg hA.le hterm]

theorem morseRho_right_cap_lower {A B x : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hx : morseRightTurn A B + log 4 ≤ x) : B / 2 ≤ -morseRho A B x := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have he : exp (-(morseRightTurn A B + log 4)) = morseRightRootT A B / 4 := by
    rw [show -(morseRightTurn A B + log 4) = -morseRightTurn A B + -log 4 by ring,
      exp_add, exp_neg (log 4), exp_log (by norm_num : (0 : ℝ) < 4),
      exp_neg_morseRightTurn hB hAB, div_eq_mul_inv]
  have ht : exp (-x) ≤ (B / A) / 2 := by
    calc
      _ ≤ exp (-(morseRightTurn A B + log 4)) := exp_le_exp.mpr (neg_le_neg hx)
      _ = morseRightRootT A B / 4 := he
      _ ≤ (2 * (B / A)) / 4 :=
        div_le_div_of_nonneg_right (morseRightRootT_ratio_bounds hB hAB).2 (by norm_num)
      _ = _ := by ring
  have hcancel : A * (B / A) = B := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hA.ne']
  have hAt : A * exp (-x) ≤ B / 2 := by
    calc
      _ ≤ A * ((B / A) / 2) := mul_le_mul_of_nonneg_left ht hA.le
      _ = (A * (B / A)) / 2 := (mul_div_assoc _ _ _).symm
      _ = _ := by rw [hcancel]
  have hterm := mul_le_mul_of_nonneg_left
    (sub_le_self (exp (-x)) (sq_nonneg (exp (-x)))) hA.le
  unfold morseRho
  rw [morse_exp_two]
  linarith only [hterm, hAt]

theorem hasDerivAt_morseRho (A B x : ℝ) :
    HasDerivAt (morseRho A B) (A * (exp (-x) * (2 * exp (-x) - 1))) x := by
  have h₁ := ((hasDerivAt_id x).neg).exp
  have h₂ := ((hasDerivAt_id x).const_mul (-2 : ℝ)).exp
  have h := ((h₁.sub h₂).const_mul A).sub_const B
  change HasDerivAt (morseRho A B) _ x at h
  convert h using 1
  simp only [Pi.neg_apply, id_eq, morse_exp_two]
  ring

theorem morseRho_deriv_left_turn_pos {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    0 < deriv (morseRho A B) (morseLeftTurn A B) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL := (morseRootT_bounds hB hAB).2.2.1
  rw [(hasDerivAt_morseRho A B _).deriv, exp_neg_morseLeftTurn hB hAB]
  exact mul_pos hA (mul_pos (by linarith) (by linarith))

theorem morseRho_deriv_right_turn_neg {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    deriv (morseRho A B) (morseRightTurn A B) < 0 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  obtain ⟨hR, hRhi, _, _⟩ := morseRootT_bounds hB hAB
  rw [(hasDerivAt_morseRho A B _).deriv, exp_neg_morseRightTurn hB hAB]
  exact mul_neg_of_pos_of_neg hA (mul_neg_of_pos_of_neg hR (by linarith))

end ContinuousFlexibility.Radial
