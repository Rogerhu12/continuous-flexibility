module

public import ContinuousFlexibility.Radial.MorseTransitionBands

/-!
# Counting the excluded heights over all frequency bands

Each frequency band `n` contains at most `radialFrequencyThreshold T C n + 1`
integers, and this threshold is at most `2 C q_n exp (n² / 2)` for the actual
Morse integers.  Hence the excluded height measures `192 c₀ exp (-n²)`, summed
over all pairs `(n, j)` of a band and an even frequency in it, are smaller than
one once `c₀` is small.  This is the union bound of the flat-end chain section
(`eq:rad-eq-rm21`, `eq:rad-eq-js13`).
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open scoped ENNReal

private theorem heightBand_q_polynomial_bound (n : ℕ) :
    Statements.radialQ n ≤ (exp 1 + 1) * ((n : ℝ) + 1) ^ 4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h₁ : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith only [hn]
  have hlog1 : 1 ≤ log (exp 1 + (n : ℝ)) := by
    calc
      1 = log (exp 1) := (log_exp 1).symm
      _ ≤ _ := log_le_log (exp_pos _) (le_add_of_nonneg_right hn)
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
      mul_le_mul hpow hlog (zero_le_one.trans hlog1) (by positivity)
    _ = _ := by ring

private theorem heightBand_nat_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith

private theorem heightBand_succ_pow_le (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 ≤ 16 * (n : ℝ) ^ 4 + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
    have h2 : ((n : ℝ) + 1) ^ 4 ≤ (2 * (n : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    nlinarith

/-- The majorant of the weighted band count. -/
def heightBandMajorant (C : ℝ) (n : ℕ) : ℝ :=
  2 * C * Statements.radialQ n * exp (-(n : ℝ) ^ 2 / 2) + exp (-(n : ℝ) ^ 2)

theorem heightBandMajorant_nonneg {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ heightBandMajorant C n := by
  have hQ : 0 ≤ Statements.radialQ n := (sq_nonneg _).trans (radial_nat_sq_le_Q n)
  unfold heightBandMajorant
  positivity

theorem heightBandMajorant_summable (C : ℝ) :
    Summable (heightBandMajorant C) := by
  have hE : Summable fun n : ℕ => exp (-(n : ℝ) ^ 2) := by
    refine Real.summable_exp_neg_nat.of_nonneg_of_le (fun _ => (exp_pos _).le) (fun n => ?_)
    exact exp_le_exp.mpr (neg_le_neg (heightBand_nat_le_sq n))
  have hP : Summable fun n : ℕ =>
      (exp 1 + 1) * (16 * ((n : ℝ) ^ 4 * exp (-(1 / 2 : ℝ) * n)) +
        (n : ℝ) ^ 0 * exp (-(1 / 2 : ℝ) * n)) :=
    (((Real.summable_pow_mul_exp_neg_nat_mul 4 (by norm_num : (0 : ℝ) < 1 / 2)).mul_left 16).add
      (Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 1 / 2))).mul_left _
  have hQ : Summable fun n : ℕ => Statements.radialQ n * exp (-(n : ℝ) ^ 2 / 2) := by
    refine hP.of_nonneg_of_le (fun n => mul_nonneg
      ((sq_nonneg _).trans (radial_nat_sq_le_Q n)) (exp_pos _).le) (fun n => ?_)
    have hexp : exp (-(n : ℝ) ^ 2 / 2) ≤ exp (-(1 / 2 : ℝ) * n) := by
      apply exp_le_exp.mpr
      have := heightBand_nat_le_sq n
      linarith
    have hpoly := heightBand_succ_pow_le n
    have hq := heightBand_q_polynomial_bound n
    have hQ0 : 0 ≤ Statements.radialQ n := (sq_nonneg _).trans (radial_nat_sq_le_Q n)
    have he0 : 0 ≤ exp (-(1 / 2 : ℝ) * n) := (exp_pos _).le
    have hb : Statements.radialQ n ≤ (exp 1 + 1) * (16 * (n : ℝ) ^ 4 + 1) :=
      hq.trans (mul_le_mul_of_nonneg_left hpoly (by positivity))
    calc
      _ ≤ Statements.radialQ n * exp (-(1 / 2 : ℝ) * n) := mul_le_mul_of_nonneg_left hexp hQ0
      _ ≤ (exp 1 + 1) * (16 * (n : ℝ) ^ 4 + 1) * exp (-(1 / 2 : ℝ) * n) :=
        mul_le_mul_of_nonneg_right hb he0
      _ = _ := by ring
  have hQ' := hQ.mul_left (2 * C)
  refine (hQ'.add hE).congr (fun n => ?_)
  unfold heightBandMajorant
  ring

/-- For the actual Morse integers the frequency threshold grows at most like
`2 C q_n exp (n² / 2)`. -/
theorem radialFrequencyThreshold_le_exp (T : Statements.MorseChainData) {C : ℝ} (hC : 0 ≤ C)
    (n : ℕ) (hd : T.d n = morseChainInteger n) :
    Statements.radialFrequencyThreshold T C n ≤
      2 * C * Statements.radialQ n * exp ((n : ℝ) ^ 2 / 2) := by
  have hQ : 0 ≤ Statements.radialQ n := (sq_nonneg _).trans (radial_nat_sq_le_Q n)
  set E : ℝ := exp ((n : ℝ) ^ 2 / 2) with hEdef
  have hE : 0 < E := exp_pos _
  have hEE : E * E = exp ((n : ℝ) ^ 2) := by rw [hEdef, ← exp_add]; ring_nf
  have hA := (morseChainA_exp_bounds T n hd).1
  have hs : 0 < E⁻¹ / 2 := by positivity
  have hsq : E⁻¹ / 2 ≤ sqrt (Statements.morseChainA T n) := by
    rw [Real.le_sqrt' hs]
    refine le_trans ?_ hA
    rw [exp_neg, ← hEE, mul_inv]
    have hi : 0 < E⁻¹ * E⁻¹ := by positivity
    nlinarith
  unfold Statements.radialFrequencyThreshold
  calc
    _ ≤ C * Statements.radialQ n / (E⁻¹ / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hC hQ) hs hsq
    _ = _ := by field_simp

/-- The union bound for the excluded heights over all frequency bands. -/
theorem exists_height_tolerance_band_sum_lt (T : Statements.MorseChainData) {C : ℝ} (hC : 0 < C)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 48 ∧
      ∑' p : {p : ℕ × ℕ // 2 ≤ p.2 ∧ Even p.2 ∧ Statements.radialFrequencyBand T C p.1 p.2},
        ENNReal.ofReal (192 * (c₀ * Real.exp (-((p.1.1 : ℕ) : ℝ) ^ 2))) < 1 := by
  set S : ℝ := ∑' n, heightBandMajorant C n with hSdef
  have hS : 0 ≤ S := tsum_nonneg (heightBandMajorant_nonneg hC.le)
  set c₀ : ℝ := min (1 / 48) (1 / (384 * (S + 1))) with hc₀def
  have hc₀ : 0 < c₀ := lt_min (by norm_num) (by positivity)
  have hc₀S : c₀ * (384 * (S + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨c₀, hc₀, min_le_left _ _, ?_⟩
  let a : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (192 * (c₀ * exp (-(n : ℝ) ^ 2)))
  let N : ℕ → ℕ := fun n => ⌈Statements.radialFrequencyThreshold T C n⌉₊
  let F : ℕ × ℕ → ℝ≥0∞ := fun q => if T.index ≤ q.1 ∧ q.2 < N q.1 then a q.1 else 0
  have hstep1 :
      ∑' p : {p : ℕ × ℕ // 2 ≤ p.2 ∧ Even p.2 ∧ Statements.radialFrequencyBand T C p.1 p.2},
        ENNReal.ofReal (192 * (c₀ * Real.exp (-((p.1.1 : ℕ) : ℝ) ^ 2))) =
      ∑' p : {p : ℕ × ℕ // 2 ≤ p.2 ∧ Even p.2 ∧ Statements.radialFrequencyBand T C p.1 p.2},
        F p.1 := by
    refine tsum_congr (fun p => ?_)
    obtain ⟨_, _, hidx, _, hlt⟩ := p.2
    have hN : p.1.2 < N p.1.1 := Nat.lt_ceil.mpr hlt
    simp only [F, a, hidx, hN, and_self, ite_true]
  have hrow : ∀ n, ∑' j, F (n, j) ≤ ENNReal.ofReal (192 * c₀ * heightBandMajorant C n) := by
    intro n
    by_cases hn : T.index ≤ n
    · have hsum : ∑' j, F (n, j) = ∑ j ∈ Finset.range (N n), a n := by
        rw [tsum_eq_sum (s := Finset.range (N n))]
        · refine Finset.sum_congr rfl (fun j hj => ?_)
          have hj' : j < N n := Finset.mem_range.mp hj
          simp only [F, hn, hj', and_self, ite_true]
        · intro j hj
          have hj' : ¬ j < N n := fun h => hj (Finset.mem_range.mpr h)
          simp only [F, hj', and_false, ite_false]
      rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have ht0 : 0 ≤ Statements.radialFrequencyThreshold T C n := by
        have hQ : 0 ≤ Statements.radialQ n := (sq_nonneg _).trans (radial_nat_sq_le_Q n)
        unfold Statements.radialFrequencyThreshold
        positivity
      have hNle : (N n : ℝ) ≤ Statements.radialFrequencyThreshold T C n + 1 :=
        (Nat.ceil_lt_add_one ht0).le
      have ht := radialFrequencyThreshold_le_exp T hC.le n (hd n hn)
      have he : exp ((n : ℝ) ^ 2 / 2) * exp (-(n : ℝ) ^ 2) = exp (-(n : ℝ) ^ 2 / 2) := by
        rw [← exp_add]; ring_nf
      have he0 : 0 ≤ exp (-(n : ℝ) ^ 2) := (exp_pos _).le
      have hNe : (N n : ℝ) * exp (-(n : ℝ) ^ 2) ≤ heightBandMajorant C n := by
        calc
          _ ≤ (2 * C * Statements.radialQ n * exp ((n : ℝ) ^ 2 / 2) + 1) * exp (-(n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) he0
          _ = 2 * C * Statements.radialQ n * (exp ((n : ℝ) ^ 2 / 2) * exp (-(n : ℝ) ^ 2)) +
              exp (-(n : ℝ) ^ 2) := by ring
          _ = _ := by rw [he]; rfl
      calc
        _ = 192 * c₀ * ((N n : ℝ) * exp (-(n : ℝ) ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hNe (by positivity)
    · have hzero : ∀ j, F (n, j) = 0 := fun j => by simp only [F, hn, false_and, ite_false]
      simp only [hzero, tsum_zero]
      exact zero_le
  have hsumm := (heightBandMajorant_summable C).mul_left (192 * c₀)
  calc
    _ = _ := hstep1
    _ ≤ ∑' q, F q := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective F
    _ = ∑' n, ∑' j, F (n, j) := ENNReal.tsum_prod'
    _ ≤ ∑' n, ENNReal.ofReal (192 * c₀ * heightBandMajorant C n) := ENNReal.tsum_le_tsum hrow
    _ = ENNReal.ofReal (∑' n, 192 * c₀ * heightBandMajorant C n) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (by positivity) (heightBandMajorant_nonneg hC.le n)) hsumm).symm
    _ = ENNReal.ofReal (192 * c₀ * S) := by rw [tsum_mul_left]
    _ < 1 := by
      rw [ENNReal.ofReal_lt_one]
      nlinarith [mul_nonneg hc₀.le hS]

/-- The same union bound for a chain whose integers are all the canonical ones. -/
theorem exists_height_tolerance_band_sum_lt_of_eq (T : Statements.MorseChainData) {C : ℝ}
    (hC : 0 < C) (hd : ∀ n, T.d n = morseChainInteger n) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 48 ∧
      ∑' p : {p : ℕ × ℕ // 2 ≤ p.2 ∧ Even p.2 ∧ Statements.radialFrequencyBand T C p.1 p.2},
        ENNReal.ofReal (192 * (c₀ * Real.exp (-((p.1.1 : ℕ) : ℝ) ^ 2))) < 1 :=
  exists_height_tolerance_band_sum_lt T hC (fun n _ => hd n)

end ContinuousFlexibility.Radial
