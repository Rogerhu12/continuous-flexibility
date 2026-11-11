import ContinuousFlexibility.Radial.OuterJoinCoefficients
import ContinuousFlexibility.Radial.OuterCellScale

/-!
# The actual preceding connector on the frequency-band scale

Both individual coefficient integrals have a quadratic exponential
bound.  Their product has the sharper cap-action bound proved from the
actual adjacent Morse geometry.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

theorem outer_exp_pow_nat (x : ℝ) (k : ℕ) :
    exp x ^ k = exp ((k : ℝ) * x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← exp_add]
      congr 1
      push_cast
      ring

theorem outer_amplitude_ratio_le_exp_sq
    (T : MorseChainData) (σ : ℕ → ℝ) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    {n p q : ℕ} (hn : 1 ≤ n) (hp : p ≤ n) (hq : q ≤ n)
    (hNp : T.index ≤ p) (hNq : T.index ≤ q)
    (hclose : p = q ∨ p = q + 1 ∨ q = p + 1) :
    morseChainAmplitude T σ p / morseChainAmplitude T σ q ≤ exp (27 * (n : ℝ) ^ 2) := by
  rcases hclose with he | hadj
  · subst p
    rw [div_self (morseChainAmplitude_pos T σ hσ q).ne']
    exact one_le_exp_iff.mpr (by positivity)
  · have hlog := morseAdjacentScale_amplitude_log_bound T σ hσ hNq hNp hadj
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hq' : (q : ℝ) ≤ n := by exact_mod_cast hq
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg q : (0 : ℝ) ≤ q) hq' 2
    have hquad : (q : ℝ) ^ 2 + 25 * (q : ℝ) + 1 ≤ 27 * (n : ℝ) ^ 2 := by
      nlinarith only [hq', hsq, hn', sq_nonneg ((n : ℝ) - 1)]
    have hpq : 0 < morseChainAmplitude T σ p / morseChainAmplitude T σ q :=
      div_pos (morseChainAmplitude_pos T σ hσ p) (morseChainAmplitude_pos T σ hσ q)
    simpa only [exp_log hpq] using exp_le_exp.mpr (hlog.trans hquad)

def outerJoinPrefactor (C : ℕ → ℝ) (K a : ℝ) : ℝ :=
  1 + C 0 * K * 9 ^ 12 * 243 + 9 * K / a

def outerJoinActionCoefficient (C : ℕ → ℝ) (K a : ℝ) : ℝ :=
  (C 0 * K ^ 2 / a) * exp 400

theorem morse_preceding_join_factor_le_frequency_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale : ℝ} {n j : ℕ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (side : Bool) (hn : T.index < n) (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2)) :
    outerPositivePhysicalFactor D (j : ℝ) scale
        (T.joinLeft side (n - 1)) (T.joinRight side (n - 1)) ≤
      exp ((4 * (outerJoinPrefactor C K D.a + (outerFrequencyExponent Cstar + L + 32)) + 2) *
        (n : ℝ) ^ 2 + 2 * sqrt (outerJoinActionCoefficient C K D.a) *
          ((j : ℝ) * sqrt (morseChainA T n))) := by
  let p := if side then n - 1 else n
  let q := if side then n else n - 1
  let N := (n : ℝ) ^ 2
  let F := outerFrequencyExponent Cstar
  let P := F + L + 32
  let U := C 0 * K * 9 ^ 12 * 243
  let V := 9 * K / D.a
  let J := outerJoinPrefactor C K D.a
  let G := outerJoinActionCoefficient C K D.a
  let a := ∫ x in T.joinLeft side (n - 1)..T.joinRight side (n - 1), scale / D.w x
  let b := ∫ x in T.joinLeft side (n - 1)..T.joinRight side (n - 1),
    (j : ℝ) ^ 2 * deriv D.w x / (scale * x)
  have hn1 : 1 ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hN : 1 ≤ N := by dsimp only [N]; nlinarith only [hn', sq_nonneg ((n : ℝ) - 1)]
  have hN₀ : 0 ≤ N := zero_le_one.trans hN
  have hk : T.index ≤ n - 1 := by omega
  have hpred : n - 1 + 1 = n := by omega
  have hp : p ≤ n := by dsimp only [p]; split <;> omega
  have hq : q ≤ n := by dsimp only [q]; split <;> omega
  have hNp : T.index ≤ p := by dsimp only [p]; split <;> omega
  have hNq : T.index ≤ q := by dsimp only [q]; split <;> omega
  have hnp : n = p ∨ n = p + 1 ∨ p = n + 1 := by dsimp only [p]; split <;> omega
  have hqn : q = n ∨ q = n + 1 ∨ n = q + 1 := by dsimp only [q]; split <;> omega
  have hK : 0 < K := hcell.pos
  have hC : 0 < C 0 := h.constants_pos 0
  have ha : 0 < D.a := h.geometry.1
  have hF : 0 ≤ F := by dsimp only [F, outerFrequencyExponent]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hJ : 0 ≤ J := by dsimp only [J, outerJoinPrefactor]; positivity
  have hG : 0 ≤ G := by dsimp only [G, outerJoinActionCoefficient]; positivity
  have hlam : 0 < morseChainAmplitude T σ n := morseChainAmplitude_pos T σ hσ n
  have hlamp : 0 < morseChainAmplitude T σ p := morseChainAmplitude_pos T σ hσ p
  have hlamq : 0 < morseChainAmplitude T σ q := morseChainAmplitude_pos T σ hσ q
  have hAp : 0 < morseChainA T p :=
    (by positivity : 0 < exp (-(p : ℝ) ^ 2) / 3).trans_le (morseChainA_exp_bounds T p (h.d_eq p hNp)).1
  have hAq : 0 < morseChainA T q :=
    (by positivity : 0 < exp (-(q : ℝ) ^ 2) / 3).trans_le (morseChainA_exp_bounds T q (h.d_eq q hNq)).1
  have hAn : 0 < morseChainA T n :=
    (by positivity : 0 < exp (-(n : ℝ) ^ 2) / 3).trans_le (morseChainA_exp_bounds T n (h.d_eq n hn.le)).1
  have hAp9 := morseChainA_le_nine T p (h.d_eq p hNp)
  have hAq9 := morseChainA_le_nine T q (h.d_eq q hNq)
  have hmax : max (morseChainA T p) (morseChainA T q) ≤ 9 := max_le hAp9 hAq9
  have hscaleP : scale / morseChainAmplitude T σ p ≤ exp ((L + 27) * N) := by
    have hr := outer_amplitude_ratio_le_exp_sq T σ hσ hn1 (le_refl n) hp hn.le hNp hnp
    calc
      _ = (scale / morseChainAmplitude T σ n) *
          (morseChainAmplitude T σ n / morseChainAmplitude T σ p) := by
        field_simp [hlam.ne', hlamp.ne'] <;> ring
      _ ≤ exp (L * N) * exp (27 * N) :=
        mul_le_mul hhi hr (div_pos hlam hlamp).le (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hscaleQ : morseChainAmplitude T σ q / scale ≤ exp ((L + 27) * N) := by
    have hr := outer_amplitude_ratio_le_exp_sq T σ hσ hn1 hq (le_refl n) hNq hn.le hqn
    calc
      _ = (morseChainAmplitude T σ q / morseChainAmplitude T σ n) *
          (morseChainAmplitude T σ n / scale) := by field_simp [hlam.ne', hscale.ne'] <;> ring
      _ ≤ exp (27 * N) * exp (L * N) :=
        mul_le_mul hr hlo (div_pos hlam hscale).le (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hInv : (morseChainA T p)⁻¹ ≤ 3 * exp N := by
    have hp' : (p : ℝ) ≤ n := by exact_mod_cast hp
    have hp2 : (p : ℝ) ^ 2 ≤ N := pow_le_pow_left₀ (Nat.cast_nonneg p) hp' 2
    have hlow : exp (-N) / 3 ≤ morseChainA T p :=
      (div_le_div_of_nonneg_right (exp_le_exp.mpr (neg_le_neg hp2)) (by norm_num)).trans
        (morseChainA_exp_bounds T p (h.d_eq p hNp)).1
    calc
      _ ≤ (exp (-N) / 3)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < exp (-N) / 3) hlow
      _ = 3 * exp N := by rw [exp_neg]; field_simp [exp_ne_zero N] <;> ring
  have hraw := morseRealizedJoin_state_integrals (j := (j : ℝ)) h hσ hcell hscale side (n - 1) hk
  dsimp only at hraw
  simp only [hpred] at hraw
  have ha₀ : 0 ≤ a := hraw.1
  have hb₀ : 0 ≤ b := hraw.2.1
  have haBound : a ≤ U * exp ((L + 32) * N) := by
    calc
      _ ≤ C 0 * K * (max (morseChainA T p) (morseChainA T q)) ^ 12 *
          (scale / morseChainAmplitude T σ p) * (morseChainA T p)⁻¹ ^ 5 := hraw.2.2.1
      _ ≤ C 0 * K * 9 ^ 12 * exp ((L + 27) * N) * (3 * exp N) ^ 5 :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (le_max_of_le_left hAp.le) hmax 12) (mul_pos hC hK).le)
            hscaleP (div_pos hscale hlamp).le (by positivity))
          (pow_le_pow_left₀ (inv_pos.mpr hAp).le hInv 5) (by positivity) (by positivity)
      _ = U * exp ((L + 32) * N) := by
        rw [mul_pow, outer_exp_pow_nat]
        dsimp only [U]
        norm_num only [Nat.cast_ofNat, show (3 : ℝ) ^ 5 = 243 by norm_num]
        rw [show C 0 * K * 9 ^ 12 * exp ((L + 27) * N) * (243 * exp ((5 : ℝ) * N)) =
          (C 0 * K * 9 ^ 12 * 243) * (exp ((L + 27) * N) * exp (5 * N)) by ring,
          ← exp_add]
        congr 2
        ring
  have hj2 : (j : ℝ) ^ 2 ≤ exp (F * N) := outer_frequency_sq_le_exp hn1 (h.d_eq n hn.le) hband
  have hbBound : b ≤ V * exp ((F + L + 27) * N) := by
    calc
      _ ≤ (K / D.a) * (j : ℝ) ^ 2 * (morseChainAmplitude T σ q / scale) *
          morseChainA T q := hraw.2.2.2
      _ ≤ (K / D.a) * exp (F * N) * exp ((L + 27) * N) * 9 :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hj2 (div_pos hK ha).le)
            hscaleQ (div_pos hlamq hscale).le (by positivity))
          hAq9 hAq.le (by positivity)
      _ = V * exp ((F + L + 27) * N) := by
        dsimp only [V]
        rw [show (K / D.a) * exp (F * N) * exp ((L + 27) * N) * 9 =
          (9 * K / D.a) * (exp (F * N) * exp ((L + 27) * N)) by ring,
          ← exp_add]
        congr 2
        ring
  have hsize : 1 + a + b ≤ J * exp (P * N) := by
    have he : 1 ≤ exp (P * N) := one_le_exp_iff.mpr (by dsimp only [P]; positivity)
    have hpa : exp ((L + 32) * N) ≤ exp (P * N) :=
      exp_le_exp.mpr (by dsimp only [P]; nlinarith only [mul_nonneg hF hN₀])
    have hpb : exp ((F + L + 27) * N) ≤ exp (P * N) :=
      exp_le_exp.mpr (by dsimp only [P]; nlinarith only [hN₀])
    have hba := haBound.trans (mul_le_mul_of_nonneg_left hpa hU)
    have hbb := hbBound.trans (mul_le_mul_of_nonneg_left hpb hV)
    have hJdef : J = 1 + U + V := rfl
    rw [hJdef]
    nlinarith only [he, hba, hbb]
  have hprod : a * b ≤ G * (j : ℝ) ^ 2 * morseChainA T n := by
    have hbal := morseRealizedJoin_balanced_product_le h hσ hcell side (n - 1) hk
    dsimp only at hbal
    simp only [hpred] at hbal
    have hmin : min (morseChainA T p) (morseChainA T q) ≤ morseChainA T n := by
      cases side with
      | false => exact min_le_left _ _
      | true => exact min_le_right _ _
    have heq := outer_state_integral_identities D (j : ℝ) scale
      (T.joinLeft side (n - 1)) (T.joinRight side (n - 1))
    change (∫ x in _.._, scale / D.w x) * (∫ x in _.._, (j : ℝ) ^ 2 * deriv D.w x / (scale * x)) ≤ _
    rw [heq.1, heq.2]
    calc
      _ = (j : ℝ) ^ 2 *
          ((∫ x in T.joinLeft side (n - 1)..T.joinRight side (n - 1), (D.w x)⁻¹) *
            (∫ x in T.joinLeft side (n - 1)..T.joinRight side (n - 1), deriv D.w x / x)) := by
        field_simp [hscale.ne'] <;> ring
      _ ≤ (j : ℝ) ^ 2 * (G * min (morseChainA T p) (morseChainA T q)) :=
        mul_le_mul_of_nonneg_left hbal (sq_nonneg _)
      _ ≤ (j : ℝ) ^ 2 * (G * morseChainA T n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hG) (sq_nonneg _)
      _ = _ := by ring
  exact outer_positive_factor_le_exp hN hJ hG hAn.le (Nat.cast_nonneg j)
    (by linarith only [ha₀, hb₀] : 0 ≤ 1 + a + b) hsize hprod

end ContinuousFlexibility.Radial
