import ContinuousFlexibility.Radial.InnerMorseOrderedConstruction
import ContinuousFlexibility.Radial.InnerMorseBufferCoefficients

/-!
# Constructing all earlier compressed Morse models after one choice

The original compression theorem is applied only after its tolerance
has been derived from the raw chain data. The constants are chosen before
the actual tail realization; the index may subsequently meet any given
lower cutoff and any prescribed error tolerance. The same construction
works for every frequency in every later band, without an upper bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

def innerMorseCompressionAmplitude : ℝ := (16 * (3 : ℝ) ^ 9) ^ 3

theorem innerMorseCompressionAmplitude_ge_one : 1 ≤ innerMorseCompressionAmplitude := by
  norm_num [innerMorseCompressionAmplitude]

/-- The raw R09 tolerance is bounded by a single fixed-degree envelope.
The larger degree eighty also accommodates the later physical remainder
and weighted conormal envelopes. -/
theorem innerMorse_compression_envelope_le {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {cost : ℕ → ℝ} (hreal : MorseChainRealization T σ D cost)
    {m j : ℕ} (hm : T.index ≤ m) (hj : 2 ≤ j)
    (hB : BufferHypotheses (innerMorseBufferData (morseChainA T m) (morseChainB T m)
      j (8 * (T.d m : ℝ) ^ 9)))
    (hact : ∀ i, innerMorseBufferActionScale * ((j : ℝ) * sqrt (morseChainA T m)) ≤
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)).action i)
    {A : ℝ} (hA : innerMorseCompressionAmplitude ≤ A) (i : Fin 2) :
    let B := innerMorseBufferData (morseChainA T m) (morseChainB T m)
      j (8 * (T.d m : ℝ) ^ 9)
    B.B₀ * B.mass i ^ 2 * exp (-B.action i) ≤
      A * radialE m ^ (80 : ℝ) * (1 + (j : ℝ)) ^ (2 : ℝ) *
        exp (-innerMorseBufferActionScale * ((j : ℝ) * sqrt (morseChainA T m))) := by
  dsimp only
  have hdNat : 2 ≤ T.d m := by
    rw [hreal.d_eq m hm]
    exact morseChainInteger_ge_two m
  have hd : (2 : ℝ) ≤ T.d m := by exact_mod_cast hdNat
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hc := innerMorseChain_buffer_coefficient_bounds T m hd hj1
  have hcE := innerMorseBufferCoefficient_le_weight T m (hreal.d_eq m hm)
  have hcube : innerMorseBufferCoefficient T m ^ 3 ≤
      innerMorseCompressionAmplitude * radialE m ^ (27 : ℝ) := by
    have h := pow_le_pow_left₀ (zero_le_one.trans hc.1) hcE 3
    rw [rpow_ofNat, mul_pow, ← pow_mul] at h
    simpa only [innerMorseCompressionAmplitude, rpow_ofNat, Nat.reduceMul] using h
  have hE1 : 1 ≤ radialE m := one_le_exp_iff.mpr (radialQ_nonneg m)
  have hpower : radialE m ^ (27 : ℝ) ≤ radialE m ^ (80 : ℝ) :=
    rpow_le_rpow_of_exponent_le hE1 (by norm_num)
  have hcommon : innerMorseBufferCoefficient T m ^ 3 ≤ A * radialE m ^ (80 : ℝ) :=
    hcube.trans (mul_le_mul hA hpower (rpow_nonneg (zero_le_one.trans hE1) _)
      (zero_le_one.trans (innerMorseCompressionAmplitude_ge_one.trans hA)))
  have hcompression := innerBuffer_compression_coefficient_envelope hB hc.1
    (Nat.cast_nonneg j) hc.2.1 hc.2.2.2.2 hact i
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcommon (sq_nonneg (1 + (j : ℝ))))
    (exp_pos (-(innerMorseBufferActionScale * ((j : ℝ) * sqrt (morseChainA T m))))).le
  simpa only [rpow_two, neg_mul] using hcompression.trans hbound

/-- Actual localized Dirichlet inverses and Poisson columns for every
retained earlier Morse cell, obtained from R09 with its original
hypotheses. No compressed model or smallness estimate is assumed. -/
theorem exists_innerMorseLocalizedChoices (hR09 : R09Statement) (a : ℝ) :
    ∃ C K ε : ℝ, 0 < C ∧ 0 < K ∧ 0 < ε ∧
      ∀ A : ℝ, innerMorseCompressionAmplitude ≤ A →
      ∃ Cstar : ℝ, 0 < Cstar ∧ innerMorseBufferThreshold ≤ Cstar ∧
        ∀ η : ℝ, 0 < η → ∀ initial : ℕ, ∃ N : ℕ,
          initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
          ∀ (T : MorseChainData) (σ : ℕ → ℝ) (D : ReferenceData) (cost : ℕ → ℝ),
            MorseChainRealization T σ D cost → T.index = N →
            ∀ m n j : ℕ, N ≤ m → m < n → 2 ≤ j → radialFrequencyBand T Cstar n j →
              Nonempty (InnerBufferLocalizedData
                (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                  (8 * (T.d m : ℝ) ^ 9)) C K) ∧
              A * radialE m ^ (80 : ℝ) * (1 + (j : ℝ)) ^ (2 : ℝ) *
                exp (-innerMorseBufferActionScale * ((j : ℝ) * sqrt (morseChainA T m))) < η ∧
              (j : ℝ) * (A * radialE m ^ (80 : ℝ) * (1 + (j : ℝ)) ^ (2 : ℝ) *
                exp (-innerMorseBufferActionScale * ((j : ℝ) * sqrt (morseChainA T m)))) < η := by
  obtain ⟨C, ε, hC, hε, hcompress⟩ := hR09 4 (by norm_num)
  obtain ⟨K, hK, hlocalized⟩ := exists_innerBufferLocalizedData
  refine ⟨C, K, ε, hC, hK, hε, ?_⟩
  intro A hA
  obtain ⟨Cstar, hCstar, hgeometry, hchoice⟩ := exists_inner_morse_model_choices a
    (p := 80) (b := 2) (A := A) (c := innerMorseBufferActionScale)
    (by norm_num) (by norm_num) (innerMorseCompressionAmplitude_ge_one.trans hA)
    innerMorseBufferActionScale_pos
  refine ⟨Cstar, hCstar, hgeometry, ?_⟩
  intro η hη initial
  obtain ⟨N, hN, hlarge, hweight, hmodels⟩ :=
    hchoice (min ε η) (lt_min hε hη) initial
  refine ⟨N, hN, hlarge, hweight, ?_⟩
  intro T σ D cost hreal hindex m n j hm hmn hj hband
  have h := hmodels T σ D cost hreal hindex m n j hm hmn hj hband
  have hmIndex : T.index ≤ m := by simpa only [hindex] using hm
  have htol (i : Fin 2) :=
    (innerMorse_compression_envelope_le hreal hmIndex hj h.1 h.2.1 hA i).trans_lt
      (h.2.2.1.trans_le (min_le_left ε η))
  have hconclusion := hcompress
    (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
      (8 * (T.d m : ℝ) ^ 9)) (by exact le_rfl) h.1 htol
  exact ⟨hlocalized _ C h.1 hconclusion,
    h.2.2.1.trans_le (min_le_right ε η), h.2.2.2.trans_le (min_le_right ε η)⟩

end ContinuousFlexibility.Radial
