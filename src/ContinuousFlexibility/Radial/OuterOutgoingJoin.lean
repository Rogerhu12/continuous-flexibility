import ContinuousFlexibility.Radial.OuterCoreInterior

/-!
# The outgoing right connector to the actual deep-tail entrance

The natural right-tail mass starts at the next cell's left cut.  The
connector after the transition cell is therefore included explicitly.
Its frequency estimate uses the proved upper frequency bound, without
claiming that the same frequency belongs to the next band.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

def outerOutgoingQuadraticExponent (C : ℕ → ℝ) (K a Cstar L : ℝ) : ℝ :=
  4 * (4 * (outerJoinPrefactor C K a + (outerFrequencyExponent Cstar + (L + 27) + 32)) + 2)

def outerOutgoingActionExponent (C : ℕ → ℝ) (K a : ℝ) : ℝ :=
  12 * sqrt (outerJoinActionCoefficient C K a)

theorem outer_next_coefficient_sqrt_le (T : MorseChainData) (n : ℕ)
    (hd : T.d n = morseChainInteger n) (hd' : T.d (n + 1) = morseChainInteger (n + 1)) :
    sqrt (morseChainA T (n + 1)) ≤ 6 * sqrt (morseChainA T n) := by
  have hA : 0 ≤ morseChainA T n := sq_nonneg _
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : (n : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith only [hn₀]
  have hupper : morseChainA T (n + 1) ≤ 36 * morseChainA T n := by
    calc
      _ ≤ 9 * exp (-((n + 1 : ℕ) : ℝ) ^ 2) := (morseChainA_exp_bounds T (n + 1) hd').2
      _ ≤ 9 * exp (-(n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hsq)) (by norm_num)
      _ ≤ 27 * morseChainA T n := by
        nlinarith only [(morseChainA_exp_bounds T n hd).1]
      _ ≤ _ := by nlinarith only [hA]
  calc
    _ ≤ sqrt (36 * morseChainA T n) := sqrt_le_sqrt hupper
    _ = _ := by
      have hsqrt : sqrt (36 : ℝ) = 6 := by
        rw [show (36 : ℝ) = (6 : ℝ) ^ 2 by norm_num, sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]
      rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 36), hsqrt]

theorem morse_outgoing_join_factor_le_frequency_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale : ℝ} {n j : ℕ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (hn : T.index < n) (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2)) :
    outerPositivePhysicalFactor D (j : ℝ) scale (T.joinLeft true n) (T.joinRight true n) ≤
      exp (outerOutgoingQuadraticExponent C K D.a Cstar L * (n : ℝ) ^ 2 +
        outerOutgoingActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) := by
  let F := outerFrequencyExponent Cstar
  let N := (n : ℝ) ^ 2
  let N' := ((n + 1 : ℕ) : ℝ) ^ 2
  let Q := 4 * (outerJoinPrefactor C K D.a + (F + (L + 27) + 32)) + 2
  have hn1 : 1 ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnext : T.index ≤ n + 1 := by omega
  have hNN : N ≤ N' := by
    dsimp only [N, N']
    push_cast
    nlinarith only [hn']
  have hN4 : N' ≤ 4 * N := by
    dsimp only [N, N']
    push_cast
    nlinarith only [hn', sq_nonneg ((n : ℝ) - 1)]
  have hF : 0 ≤ F := by dsimp only [F, outerFrequencyExponent]; positivity
  have hlam : 0 < morseChainAmplitude T σ n := morseChainAmplitude_pos T σ hσ n
  have hlam' : 0 < morseChainAmplitude T σ (n + 1) := morseChainAmplitude_pos T σ hσ (n + 1)
  have hhi' : scale / morseChainAmplitude T σ (n + 1) ≤ exp ((L + 27) * N') := by
    have hr := outer_amplitude_ratio_le_exp_sq T σ hσ (by omega : 1 ≤ n + 1)
      (by omega : n ≤ n + 1) (le_refl (n + 1)) hn.le hnext (Or.inr (Or.inr rfl))
    have he := hhi.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hNN hL))
    calc
      _ = (scale / morseChainAmplitude T σ n) *
          (morseChainAmplitude T σ n / morseChainAmplitude T σ (n + 1)) := by
        field_simp [hlam.ne', hlam'.ne'] <;> ring
      _ ≤ exp (L * N') * exp (27 * N') :=
        mul_le_mul he hr (div_pos hlam hlam').le (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hlo' : morseChainAmplitude T σ (n + 1) / scale ≤ exp ((L + 27) * N') := by
    have hr := outer_amplitude_ratio_le_exp_sq T σ hσ (by omega : 1 ≤ n + 1)
      (le_refl (n + 1)) (by omega : n ≤ n + 1) hnext hn.le (Or.inr (Or.inl rfl))
    have he := hlo.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hNN hL))
    calc
      _ = (morseChainAmplitude T σ (n + 1) / morseChainAmplitude T σ n) *
          (morseChainAmplitude T σ n / scale) := by
        field_simp [hlam.ne', hscale.ne'] <;> ring
      _ ≤ exp (27 * N') * exp (L * N') :=
        mul_le_mul hr he (div_pos hlam hscale).le (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hj : (j : ℝ) ^ 2 ≤ exp (F * N') :=
    (outer_frequency_sq_le_exp hn1 (h.d_eq n hn.le) hband).trans
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hNN hF))
  have hbound := morse_preceding_join_factor_le_sq_exp h hσ hcell hscale
    (by linarith only [hL] : 0 ≤ L + 27) hF true (by omega : T.index < n + 1) hj hhi' hlo'
  simp only [Nat.add_sub_cancel] at hbound
  have hK : 0 < K := hcell.pos
  have hC : 0 < C 0 := h.constants_pos 0
  have ha : 0 < D.a := h.geometry.1
  have hQ : 0 ≤ Q := by dsimp only [Q, outerJoinPrefactor]; positivity
  have hrad := outer_next_coefficient_sqrt_le T n (h.d_eq n hn.le) (h.d_eq (n + 1) hnext)
  have htau := mul_le_mul_of_nonneg_left hrad (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hquad := mul_le_mul_of_nonneg_left hN4 hQ
  have haction := mul_le_mul_of_nonneg_left htau
    (by positivity : 0 ≤ 2 * sqrt (outerJoinActionCoefficient C K D.a))
  apply hbound.trans
  apply exp_le_exp.mpr
  dsimp only [outerOutgoingQuadraticExponent, outerOutgoingActionExponent, Q, F, N, N'] at *
  nlinarith only [hquad, haction]

end ContinuousFlexibility.Radial
