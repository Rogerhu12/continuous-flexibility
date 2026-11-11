import ContinuousFlexibility.Radial.InnerModelCoefficientEnvelope
import ContinuousFlexibility.Radial.InnerMorseBufferBounds

/-!
# Ordered choices for the actual Morse models and their envelopes

The frequency threshold accommodates both the raw buffer geometry and
the coefficient powers. It is fixed before the starting index and before
any realization of either tail. Every later frequency, however large,
then yields the actual buffer hypotheses, its action lower bound, and
small polynomial-exponential errors including an extra frequency factor.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

/-- A preassigned geometric threshold may be imposed without changing
the order of choices or restricting the range of later frequencies. -/
theorem inner_ordered_morse_choices_of_threshold (a : ℝ)
    {c₁ c₂ c₃ Cstar : ℝ} (hc₂ : 0 ≤ c₂) (hc₃ : 0 < c₃)
    (hCstar : 0 < Cstar) (hscale : 4 * (c₁ + 5) / c₃ ≤ Cstar)
    {η : ℝ} (hη : 0 < η) (initial : ℕ) :
    ∃ N : ℕ, initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
      ∀ T : MorseChainData, T.index = N →
        (∀ m, N ≤ m → T.d m = morseChainInteger m) →
        ∀ m n j : ℕ, N ≤ m → m < n → radialFrequencyBand T Cstar n j →
          exp (c₁ * radialQ m + c₂ * log (1 + (j : ℝ) * sqrt (morseChainA T m)) -
            c₃ * ((j : ℝ) * sqrt (morseChainA T m))) < η ∧
          (j : ℝ) * exp (c₁ * radialQ m +
            c₂ * log (1 + (j : ℝ) * sqrt (morseChainA T m)) -
            c₃ * ((j : ℝ) * sqrt (morseChainA T m))) < η := by
  obtain ⟨N, hN, hlarge, hweight, hsmall⟩ := inner_uniform_frequency_suppression
    radialQ inner_radialQ_tendsto a initial hc₂ hc₃ hCstar hscale hη
  refine ⟨N, hN, hlarge, hweight, ?_⟩
  intro T hindex hd m n j hm hmn hband
  have hmIndex : T.index ≤ m := by simpa only [hindex] using hm
  have hd' : ∀ k, T.index ≤ k → T.d k = morseChainInteger k := by
    intro k hk
    exact hd k (by simpa only [hindex] using hk)
  have haction := morseTransition_earlier_cap_action T hCstar hd' hband hmIndex hmn
  have hm1 : 1 ≤ m := by omega
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hQpos : 0 < radialQ m := lt_of_lt_of_le
    (by nlinarith only [hmReal] : (0 : ℝ) < (m : ℝ) ^ 2) (radial_nat_sq_le_Q m)
  have hj1 : 1 ≤ j := by
    by_contra h
    have hjzero : j = 0 := by omega
    rw [hjzero, Nat.cast_zero, zero_mul] at haction
    exact (not_le_of_gt (mul_pos hCstar hQpos)) haction
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hlog : log (j : ℝ) ≤
      log (1 + (j : ℝ) * sqrt (morseChainA T m)) + 5 * radialQ m :=
    (log_le_log (zero_lt_one.trans_le hj) (by linarith : (j : ℝ) ≤ 1 + (j : ℝ))).trans
      (inner_morse_frequency_log_bound T (hd m hm) hm1 (Nat.cast_nonneg j))
  exact hsmall m hm _ j haction hj hlog

/-- The same ordered choices construct the raw models and suppress all
their polynomial envelopes, uniformly for every later realization and
every admissible frequency. The starting index may depend on the weight
exponent, but the geometric action scale and polynomial degree do not. -/
theorem exists_inner_morse_model_choices (a : ℝ) {p b A c : ℝ}
    (hp : 0 ≤ p) (hb : 0 ≤ b) (hA : 1 ≤ A) (hc : 0 < c) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ innerMorseBufferThreshold ≤ Cstar ∧
      ∀ η : ℝ, 0 < η → ∀ initial : ℕ, ∃ N : ℕ,
        initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
        ∀ (T : MorseChainData) (σ : ℕ → ℝ) (D : ReferenceData) (cost : ℕ → ℝ),
          MorseChainRealization T σ D cost → T.index = N →
          ∀ m n j : ℕ, N ≤ m → m < n → 2 ≤ j → radialFrequencyBand T Cstar n j →
            BufferHypotheses (innerMorseBufferData (morseChainA T m) (morseChainB T m)
              j (8 * (T.d m : ℝ) ^ 9)) ∧
            (∀ i, innerMorseBufferActionScale * ((j : ℝ) * sqrt (morseChainA T m)) ≤
              (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                (8 * (T.d m : ℝ) ^ 9)).action i) ∧
            A * radialE m ^ p * (1 + (j : ℝ)) ^ b *
              exp (-c * ((j : ℝ) * sqrt (morseChainA T m))) < η ∧
            (j : ℝ) * (A * radialE m ^ p * (1 + (j : ℝ)) ^ b *
              exp (-c * ((j : ℝ) * sqrt (morseChainA T m)))) < η := by
  let c₁ := p + 5 * b + log A
  have hc₁ : 0 ≤ c₁ := by
    dsimp only [c₁]
    exact add_nonneg (add_nonneg hp (mul_nonneg (by norm_num) hb)) (log_nonneg hA)
  let Cstar := max innerMorseBufferThreshold (1 + 4 * (c₁ + 5) / c)
  have hCstar : 0 < Cstar := innerMorseBufferThreshold_pos.trans_le (le_max_left _ _)
  have hgeometry : innerMorseBufferThreshold ≤ Cstar := le_max_left _ _
  have hscale : 4 * (c₁ + 5) / c ≤ Cstar := by
    exact (by linarith : 4 * (c₁ + 5) / c ≤ 1 + 4 * (c₁ + 5) / c).trans
      (le_max_right _ _)
  refine ⟨Cstar, hCstar, hgeometry, ?_⟩
  intro η hη initial
  obtain ⟨N, hN, hlarge, hweight, hsmall⟩ :=
    inner_ordered_morse_choices_of_threshold a hb hc hCstar hscale hη initial
  refine ⟨N, hN, hlarge, hweight, ?_⟩
  intro T σ D cost hreal hindex m n j hm hmn hj hband
  have hmIndex : T.index ≤ m := by simpa only [hindex] using hm
  have hindex10 : 10 ≤ T.index := by omega
  have hraw := innerMorseChain_buffer hreal hgeometry hindex10 hmIndex hmn hj hband
  have hsmall' := hsmall T hindex
    (fun k hk => hreal.d_eq k (by simpa only [hindex] using hk)) m n j hm hmn hband
  have henv := inner_morse_polynomial_envelope T (hreal.d_eq m hmIndex)
    (show 1 ≤ m by omega) (Nat.cast_nonneg j) hb hA (p := p) (c := c)
  refine ⟨hraw.1, hraw.2, henv.trans_lt hsmall'.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left henv (Nat.cast_nonneg j)).trans_lt hsmall'.2

end ContinuousFlexibility.Radial
