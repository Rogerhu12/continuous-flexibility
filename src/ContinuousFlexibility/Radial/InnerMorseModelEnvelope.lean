import ContinuousFlexibility.Radial.InnerMorseModelCoefficient
import ContinuousFlexibility.Radial.InnerMorseWeights

/-!
# Closed normalized envelopes for the actual Morse models

The remainder uses the original inward energy of one localized model,
with the actual whole-cell velocity fourteen and the proved cut weight
ratio E_m. The full conormal error uses both true cut weights and both
conjugation signs. A single fixed coefficient exponent eighty controls
both quantities, and the ordered choice constructs the same model
while suppressing its error and its frequency times the remainder.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements
open scoped Matrix.Norms.L2Operator

def innerMorseModelEnvelope (T : MorseChainData) (m : ℕ) (j A : ℝ) : ℝ :=
  A * radialE m ^ (80 : ℝ) * (1 + j) ^ 2 *
    exp (-innerMorseBufferActionScale * (j * sqrt (morseChainA T m)))

def innerMorseModelNormalizedRemainder {T : MorseChainData} {m : ℕ} {j C K : ℝ}
    (M : InnerBufferLocalizedData
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)) C K) (i : Fin 2) : ℝ :=
  (sqrt 12 * 14 * radialE m + 1) *
    (innerBufferRemainderEnvelope
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)) C K i / sqrt (M.column i).inwardEnergy)

def innerMorseModelRemainderFactor (C K : ℝ) : ℝ :=
  (sqrt 12 + 1) * (2 * K * (1 + 2 * C))

def innerMorseModelErrorFactor (C : ℝ) : ℝ := 8 * C * (1 + C ^ 2)

def innerMorseModelAmplitude (C K : ℝ) : ℝ :=
  innerMorseCompressionAmplitude +
    (1 + innerMorseModelRemainderFactor C K + innerMorseModelErrorFactor C) *
      innerMorseModelCoefficientConstant C ^ 8

theorem innerMorseModelAmplitude_bounds {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    innerMorseCompressionAmplitude ≤ innerMorseModelAmplitude C K ∧
      innerMorseModelRemainderFactor C K * innerMorseModelCoefficientConstant C ^ 8 ≤
        innerMorseModelAmplitude C K ∧
      innerMorseModelErrorFactor C * innerMorseModelCoefficientConstant C ^ 8 ≤
        innerMorseModelAmplitude C K := by
  have hr : 0 ≤ innerMorseModelRemainderFactor C K := by
    unfold innerMorseModelRemainderFactor
    positivity
  have he : 0 ≤ innerMorseModelErrorFactor C := by
    unfold innerMorseModelErrorFactor
    positivity
  have hp : 0 ≤ innerMorseModelCoefficientConstant C ^ 8 := by positivity
  have ha : 0 ≤ innerMorseCompressionAmplitude :=
    zero_le_one.trans innerMorseCompressionAmplitude_ge_one
  have hrest : 0 ≤ (1 + innerMorseModelRemainderFactor C K +
      innerMorseModelErrorFactor C) * innerMorseModelCoefficientConstant C ^ 8 := by positivity
  have hr' := mul_le_mul_of_nonneg_right
    (show innerMorseModelRemainderFactor C K ≤
      1 + innerMorseModelRemainderFactor C K + innerMorseModelErrorFactor C by linarith only [he]) hp
  have he' := mul_le_mul_of_nonneg_right
    (show innerMorseModelErrorFactor C ≤
      1 + innerMorseModelRemainderFactor C K + innerMorseModelErrorFactor C by linarith only [hr]) hp
  unfold innerMorseModelAmplitude
  exact ⟨by linarith only [hrest], by linarith only [hr', ha], by linarith only [he', ha]⟩

theorem innerMorseModelNormalizedRemainder_le_envelope (T : MorseChainData) (m : ℕ)
    (hd : T.d m = morseChainInteger m) {j C K A : ℝ} (hj : 1 ≤ j)
    (hC : 0 < C) (hK : 0 ≤ K)
    (hB : BufferHypotheses
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j (8 * (T.d m : ℝ) ^ 9)))
    (M : InnerBufferLocalizedData
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)) C K)
    (hact : ∀ i, innerMorseBufferActionScale * (j * sqrt (morseChainA T m)) ≤
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)).action i)
    (hA : innerMorseModelRemainderFactor C K * innerMorseModelCoefficientConstant C ^ 8 ≤ A)
    (i : Fin 2) :
    innerMorseModelNormalizedRemainder M i ≤ innerMorseModelEnvelope T m j A := by
  obtain ⟨hc, hB0, hlayer, hinv, hmass, hU, hratio⟩ :=
    innerMorseModelCoefficient_bounds T m hd hC.le hj
  have hk := (M.energies_pos hB hC i).1
  have hkinv := innerMorseModelCoefficient_inverse_sqrt_energy T m hd hC hj i
    (M.column i).inward_lower
  have hE0 : 0 ≤ radialE m := (exp_pos _).le
  have hraw := innerBuffer_normalized_remainder_coefficient_envelope hB hC.le hK hc
    (zero_le_one.trans hj) hB0 hlayer hinv hmass hact
    (by norm_num : (0 : ℝ) ≤ 14) hE0 hU hratio hk hkinv i
  have hfactor : 0 ≤ innerMorseModelRemainderFactor C K := by
    unfold innerMorseModelRemainderFactor
    positivity
  have hpower := innerMorseModelCoefficient_pow_le hC.le hfactor hA m (le_refl 8)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpower (sq_nonneg (1 + j)))
    (exp_pos (-(innerMorseBufferActionScale * (j * sqrt (morseChainA T m))))).le
  simpa only [innerMorseModelNormalizedRemainder, innerMorseModelRemainderFactor,
    innerMorseModelEnvelope, neg_mul] using hraw.trans hbound

/-- The full two-cut error keeps the actual outward flux matrix. The
same bound handles every allowed weight parameter and both signs. -/
theorem innerMorseModelFluxError_le_envelope (T : MorseChainData) (m N : ℕ)
    (hd : T.d m = morseChainInteger m) {j C K A a γ : ℝ} (hj : 1 ≤ j)
    (hC : 0 < C) (ha : 0 ≤ a) (hγ : |γ| ≤ 1)
    (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ)) (hm : N ≤ m)
    (hB : BufferHypotheses
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j (8 * (T.d m : ℝ) ^ 9)))
    (M : InnerBufferLocalizedData
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)) C K)
    (hact : ∀ i, innerMorseBufferActionScale * (j * sqrt (morseChainA T m)) ≤
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)).action i)
    (hA : innerMorseModelErrorFactor C * innerMorseModelCoefficientConstant C ^ 8 ≤ A)
    (side : Bool) {height : ℝ} (hh : 0 < height) (sign : Bool) :
    ‖innerTwoCutWeightedError
      (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
      (innerMorseCutWeight N a γ side m) (M.physicalFluxError height (fun _ => 1)) sign‖ ≤
        innerMorseModelEnvelope T m j A := by
  obtain ⟨hc, hB0, _hlayer, _hinv, hmass, _hU, hratio⟩ :=
    innerMorseModelCoefficient_bounds T m hd hC.le hj
  have hcoeff0 : 0 ≤ innerMorseModelCoefficient C m := zero_le_one.trans hc
  have hE0 : 0 ≤ radialE m := (exp_pos _).le
  have hk := fun i => (M.energies_pos hB hC i).1
  have hraw := M.physical_error_weighted_bound hB hC height
    (fun _ => 1) (fun i => (M.column i).inwardEnergy)
    (innerMorseCutWeight N a γ side m) hh (fun _ => by norm_num) hk
    (innerMorseCutWeight_pos N a γ side m) (fun i => by linarith only [hk i]) hE0
    (innerMorseCutWeight_ratio N ha hγ hN hNa hm side) hmass hact sign
  have ht : 0 ≤ innerMorseBufferActionScale * (j * sqrt (morseChainA T m)) :=
    mul_nonneg innerMorseBufferActionScale_pos.le
      (mul_nonneg (zero_le_one.trans hj) (sqrt_nonneg _))
  have hexp : exp (-2 * (innerMorseBufferActionScale * (j * sqrt (morseChainA T m)))) ≤
      exp (-(innerMorseBufferActionScale * (j * sqrt (morseChainA T m)))) :=
    exp_le_exp.mpr (by linarith only [ht])
  have he0 : 0 ≤ innerMorseModelErrorFactor C := by
    unfold innerMorseModelErrorFactor
    positivity
  have hprod : radialE m *
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)).B₀ ≤ innerMorseModelCoefficient C m ^ 2 := by
    simpa only [pow_two] using mul_le_mul hratio hB0 hB.2.2.1.le hcoeff0
  have hbase := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ innerMorseModelErrorFactor C * innerMorseModelCoefficient C m ^ 2 *
      (1 + j) ^ 2 by positivity)
  have hpoly := mul_le_mul hbase hexp (exp_pos _).le (by positivity)
  have hpoly' : 4 * radialE m * ((2 * (1 + C ^ 2)) *
      (C * (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)).B₀ *
        (innerMorseModelCoefficient C m * (1 + j)) ^ 2 *
          exp (-2 * (innerMorseBufferActionScale * (j * sqrt (morseChainA T m)))))) ≤
      innerMorseModelErrorFactor C * innerMorseModelCoefficient C m ^ 4 *
        (1 + j) ^ 2 * exp (-(innerMorseBufferActionScale * (j * sqrt (morseChainA T m)))) := by
    calc
      _ = (innerMorseModelErrorFactor C * innerMorseModelCoefficient C m ^ 2 * (1 + j) ^ 2) *
          (radialE m * (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
            (8 * (T.d m : ℝ) ^ 9)).B₀) *
          exp (-2 * (innerMorseBufferActionScale * (j * sqrt (morseChainA T m)))) := by
        unfold innerMorseModelErrorFactor
        ring
      _ ≤ _ := hpoly
      _ = _ := by ring
  have hpower := innerMorseModelCoefficient_pow_le hC.le he0 hA m (by norm_num : 4 ≤ 8)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpower (sq_nonneg (1 + j)))
    (exp_pos (-(innerMorseBufferActionScale * (j * sqrt (morseChainA T m))))).le
  simpa only [innerMorseModelEnvelope, neg_mul] using hraw.trans (hpoly'.trans hbound)

/-- The same original R09 data gives the small full conormal error and
the frequency-small normalized physical remainder, uniformly over all
later bands and without an upper frequency cutoff. -/
theorem exists_innerMorseModelChoices (hR09 : R09Statement) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ A : ℝ, innerMorseModelAmplitude C K ≤ A →
      ∃ Cstar : ℝ, 0 < Cstar ∧ innerMorseBufferThreshold ≤ Cstar ∧
        ∀ η : ℝ, 0 < η → ∀ initial : ℕ, ∃ N : ℕ,
          initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
          ∀ (T : MorseChainData) (σ : ℕ → ℝ) (D : ReferenceData) (cost : ℕ → ℝ),
            MorseChainRealization T σ D cost → T.index = N →
            ∀ m n j : ℕ, N ≤ m → m < n → 2 ≤ j → radialFrequencyBand T Cstar n j →
              BufferHypotheses
                (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                  (8 * (T.d m : ℝ) ^ 9)) ∧
              ∃ M : InnerBufferLocalizedData
                (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                  (8 * (T.d m : ℝ) ^ 9)) C K,
                (∀ i, innerMorseModelNormalizedRemainder M i < min 1 η / (j : ℝ)) ∧
                ∀ γ : ℝ, |γ| ≤ 1 → ∀ side : Bool, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
                  ‖innerTwoCutWeightedError
                    (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
                    (innerMorseCutWeight N a γ side m)
                    (M.physicalFluxError height (fun _ => 1)) sign‖ < η := by
  obtain ⟨C, K, ε, hC, hK, _hε, hchoice⟩ := exists_innerMorseLocalizedChoices hR09 a
  refine ⟨C, K, hC, hK, ?_⟩
  intro A hA
  have hfactor := innerMorseModelAmplitude_bounds hC.le hK.le
  obtain ⟨Cstar, hCstar, hgeometry, hmodels⟩ := hchoice A (hfactor.1.trans hA)
  refine ⟨Cstar, hCstar, hgeometry, ?_⟩
  intro η hη initial
  obtain ⟨N, hN, hlarge, hweight, htail⟩ := hmodels (min 1 η) (lt_min zero_lt_one hη) initial
  refine ⟨N, hN, hlarge, hweight, ?_⟩
  intro T σ D cost hreal hindex m n j hm hmn hj hband
  obtain ⟨⟨M⟩, henv, hfreq⟩ := htail T σ D cost hreal hindex m n j hm hmn hj hband
  have hmIndex : T.index ≤ m := by simpa only [hindex] using hm
  have hraw := innerMorseChain_buffer hreal hgeometry (by omega : 10 ≤ T.index)
    hmIndex hmn hj hband
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjpos : (0 : ℝ) < j := zero_lt_one.trans_le hj1
  have hs : innerMorseModelEnvelope T m j A < min 1 η ∧
      (j : ℝ) * innerMorseModelEnvelope T m j A < min 1 η := by
    simpa only [innerMorseModelEnvelope, rpow_two] using And.intro henv hfreq
  refine ⟨hraw.1, M, ?_, ?_⟩
  · intro i
    apply (lt_div_iff₀ hjpos).mpr
    have hrem := innerMorseModelNormalizedRemainder_le_envelope T m (hreal.d_eq m hmIndex)
      hj1 hC hK.le hraw.1 M hraw.2 (hfactor.2.1.trans hA) i
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hrem hjpos.le).trans_lt hs.2
  · intro γ hγ side height hh sign
    exact (innerMorseModelFluxError_le_envelope T m N (hreal.d_eq m hmIndex)
      hj1 hC ha hγ hlarge hweight hm hraw.1 M hraw.2 (hfactor.2.2.trans hA) side hh sign).trans_lt
      (hs.1.trans_le (min_le_right 1 η))

end ContinuousFlexibility.Radial
