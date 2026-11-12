import ContinuousFlexibility.Radial.InnerMorsePhysicalPoisson

/-!
# Morse choices valid for every later starting index

The compression constants are fixed before the caller supplies a frequency
floor.  The resulting scalar threshold is independent of the chain.  Every
realized chain beginning beyond that threshold then supplies the same local
compression, physical Poisson estimate, and weighted conormal estimate.

The weights are based at the actual `T.index`, so the first retained inward
weight is one even when the selected chain begins strictly after the scalar
threshold.  The physical-column step uses the public version of the existing
`innerMorsePhysicalPoissonBound_of_remainder` theorem from `InnerMorsePhysicalPoisson`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements
open scoped Matrix.Norms.L2Operator

/-- One choice of compression constants works for every prescribed frequency
floor.  After the frequency threshold and numerical lower index are chosen,
the geometric realization may have any larger starting index. -/
theorem exists_innerMorsePhysicalChoices_atLeast
    (hR09 : R09Statement) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ Cfloor : ℝ, ∃ Cstar : ℝ,
        Cfloor ≤ Cstar ∧ 0 < Cstar ∧ innerMorseBufferThreshold ≤ Cstar ∧
        ∀ η : ℝ, 0 < η → ∀ initial : ℕ, ∃ N₀ : ℕ,
          initial ≤ N₀ ∧ 4096 ≤ N₀ ∧ 64 * a ≤ (N₀ : ℝ) ∧
          ∀ (T : MorseChainData) (σ : ℕ → ℝ) (D : ReferenceData) (cost : ℕ → ℝ),
            ∀ hreal : MorseChainRealization T σ D cost, N₀ ≤ T.index →
            ∀ m n j : ℕ, T.index ≤ m → m < n → 2 ≤ j →
              radialFrequencyBand T Cstar n j →
              BufferHypotheses
                (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                  (8 * (T.d m : ℝ) ^ 9)) ∧
              ∃ M : InnerBufferLocalizedData
                (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                  (8 * (T.d m : ℝ) ^ 9)) C K,
                (∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / (j : ℝ)) ∧
                InnerMorsePhysicalPoissonBound hreal T.index a M ∧
                ∀ γ : ℝ, |γ| ≤ 1 → ∀ side : Bool, ∀ height : ℝ,
                  0 < height → ∀ sign : Bool,
                  ‖innerTwoCutWeightedError
                    (innerPhysicalCutKappa height (fun _ => 1)
                      (fun i => (M.column i).inwardEnergy))
                    (innerMorseCutWeight T.index a γ side m)
                    (M.physicalFluxError height (fun _ => 1)) sign‖ < η := by
  obtain ⟨C, ε, hC, hε, hcompress⟩ := hR09 4 (by norm_num)
  obtain ⟨K, hK, hlocalized⟩ := exists_innerBufferLocalizedData
  refine ⟨C, K, hC, hK, ?_⟩
  intro Cfloor
  let A := innerMorseModelAmplitude C K
  have hfactor := innerMorseModelAmplitude_bounds hC.le hK.le
  have hA : 1 ≤ A := innerMorseCompressionAmplitude_ge_one.trans hfactor.1
  let c₁ : ℝ := 80 + 5 * 2 + log A
  let Cstar : ℝ := max Cfloor
    (max innerMorseBufferThreshold (1 + 4 * (c₁ + 5) / innerMorseBufferActionScale))
  have hfloor : Cfloor ≤ Cstar := le_max_left _ _
  have hgeometry : innerMorseBufferThreshold ≤ Cstar :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCstar : 0 < Cstar := innerMorseBufferThreshold_pos.trans_le hgeometry
  have hscale : 4 * (c₁ + 5) / innerMorseBufferActionScale ≤ Cstar :=
    (show 4 * (c₁ + 5) / innerMorseBufferActionScale ≤
      1 + 4 * (c₁ + 5) / innerMorseBufferActionScale by linarith).trans
        ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Cstar, hfloor, hCstar, hgeometry, ?_⟩
  intro η hη initial
  obtain ⟨N₀, hN₀, hlarge, hweight, hsmall⟩ :=
    inner_uniform_frequency_suppression radialQ inner_radialQ_tendsto a initial
      (c₁ := c₁) (c₂ := 2) (c₃ := innerMorseBufferActionScale) (r := 5)
      (Cstar := Cstar) (η := min ε (min 1 η)) (by norm_num)
      innerMorseBufferActionScale_pos hCstar hscale
      (lt_min hε (lt_min zero_lt_one hη))
  refine ⟨N₀, hN₀, hlarge, hweight, ?_⟩
  intro T σ D cost hreal hindex m n j hm hmn hj hband
  have hm₀ : N₀ ≤ m := hindex.trans hm
  have hm1 : 1 ≤ m := by omega
  have hindexLarge : 4096 ≤ T.index := hlarge.trans hindex
  have hindexWeight : 64 * a ≤ (T.index : ℝ) :=
    hweight.trans (by exact_mod_cast hindex)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjpos : (0 : ℝ) < j := zero_lt_one.trans_le hj1
  have hd := hreal.d_eq m hm
  have hraw := innerMorseChain_buffer hreal hgeometry (by omega : 10 ≤ T.index)
    hm hmn hj hband
  have haction := morseTransition_earlier_cap_action T hCstar
    (fun k hk => hreal.d_eq k hk) hband hm hmn
  have hlog : log (j : ℝ) ≤
      log (1 + (j : ℝ) * sqrt (morseChainA T m)) + 5 * radialQ m :=
    (log_le_log hjpos (by linarith : (j : ℝ) ≤ 1 + (j : ℝ))).trans
      (inner_morse_frequency_log_bound T hd hm1 (Nat.cast_nonneg j))
  have hsmall' := hsmall m hm₀ _ j haction hj1 hlog
  have hpoly : innerMorseModelEnvelope T m j A ≤
      exp (c₁ * radialQ m +
        2 * log (1 + (j : ℝ) * sqrt (morseChainA T m)) -
        innerMorseBufferActionScale * ((j : ℝ) * sqrt (morseChainA T m))) := by
    simpa only [innerMorseModelEnvelope, c₁, rpow_two] using
      (inner_morse_polynomial_envelope T hd hm1 (p := 80) (b := 2) (A := A)
        (c := innerMorseBufferActionScale) (Nat.cast_nonneg j) (by norm_num) hA)
  have hs : innerMorseModelEnvelope T m j A < min ε (min 1 η) ∧
      (j : ℝ) * innerMorseModelEnvelope T m j A < min ε (min 1 η) :=
    ⟨hpoly.trans_lt hsmall'.1,
      (mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg j)).trans_lt hsmall'.2⟩
  have heps : A * radialE m ^ (80 : ℝ) * (1 + (j : ℝ)) ^ (2 : ℝ) *
      exp (-innerMorseBufferActionScale * ((j : ℝ) * sqrt (morseChainA T m))) < ε := by
    simpa only [innerMorseModelEnvelope, rpow_two] using
      hs.1.trans_le (min_le_left ε (min 1 η))
  have htol (i : Fin 2) :=
    (innerMorse_compression_envelope_le hreal hm hj hraw.1 hraw.2 hfactor.1 i).trans_lt heps
  have hcompressed := hcompress
    (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
      (8 * (T.d m : ℝ) ^ 9)) le_rfl hraw.1 htol
  obtain ⟨M⟩ := hlocalized _ C hraw.1 hcompressed
  have hrem : ∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / (j : ℝ) := by
    intro i
    apply le_of_lt
    apply (lt_div_iff₀ hjpos).mpr
    have hi := innerMorseModelNormalizedRemainder_le_envelope T m hd hj1 hC hK.le
      hraw.1 M hraw.2 hfactor.2.1 i
    have h := (mul_le_mul_of_nonneg_left hi hjpos.le).trans_lt hs.2
    have h' : innerMorseModelNormalizedRemainder M i * (j : ℝ) < min ε (min 1 η) := by
      simpa only [mul_comm] using h
    exact h'.trans_le ((min_le_right ε (min 1 η)).trans (min_le_left 1 η))
  refine ⟨hraw.1, M, hrem,
    innerMorsePhysicalPoissonBound_of_remainder hreal T.index ha
      hindexLarge hindexWeight hm hj1 hC M hrem, ?_⟩
  intro γ hγ side height hh sign
  exact (innerMorseModelFluxError_le_envelope T m T.index hd hj1 hC ha hγ
    hindexLarge hindexWeight hm hraw.1 M hraw.2 hfactor.2.2 side hh sign).trans_lt
      (hs.1.trans_le ((min_le_right ε (min 1 η)).trans (min_le_right 1 η)))

end ContinuousFlexibility.Radial
