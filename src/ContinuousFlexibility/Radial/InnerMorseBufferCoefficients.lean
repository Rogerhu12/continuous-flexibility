module

public import ContinuousFlexibility.Radial.InnerMorseBufferBounds

/-!
# Raw coefficient costs for the actual Morse buffers

The right mass can be small. Its reciprocal, the spectral inverse,
the layer constant and the masses themselves nevertheless have one
fixed polynomial cost in the actual integer parameter. This cost is
bounded by a fixed ninth power of the manuscript's coefficient weight,
before the starting index or the frequency band is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

/-- A deliberately common coefficient for the spectral and cap data. -/
def innerMorseBufferCoefficient (T : MorseChainData) (m : ℕ) : ℝ :=
  16 * (T.d m : ℝ) ^ 9

theorem innerMorseCapMass_bounds {A B j : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA : A ≤ 9) (hB1 : B ≤ 1)
    (hj : 1 ≤ j) (right : Bool) :
    B / 2 ≤ innerMorseCapMass A B j right ∧
      innerMorseCapMass A B j right ≤ 2 * j := by
  let c : ℝ := if right then B / 2 else A / 4
  have hc : B / 2 ≤ c := by
    dsimp only [c]
    split_ifs <;> linarith only [hB, hAB]
  have hc4 : c ≤ 4 := by
    dsimp only [c]
    split_ifs <;> linarith only [hA, hB1]
  have hbase : B / 2 ≤ sqrt (B / 2) :=
    le_sqrt_self_iff.mpr (by linarith only [hB1])
  have hroot : sqrt c ≤ 2 := sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hc4]⟩
  have hj0 : 0 ≤ j := zero_le_one.trans hj
  refine ⟨?_, ?_⟩
  · calc
      B / 2 ≤ sqrt (B / 2) := hbase
      _ ≤ sqrt c := sqrt_le_sqrt hc
      _ ≤ j * sqrt c := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hj (sqrt_nonneg c)
      _ = innerMorseCapMass A B j right := rfl
  · exact (mul_le_mul_of_nonneg_left hroot hj0).trans_eq (mul_comm j 2)

/-- The inverse mass estimate is valid even on the very long, low-mass
right cap. No lower bound by one is imposed on either mass. -/
theorem innerMorseChain_buffer_mass_bounds (T : MorseChainData) (m : ℕ)
    (hd : 2 ≤ (T.d m : ℝ)) {j : ℝ} (hj : 1 ≤ j) (i : Fin 2) :
    (innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i)⁻¹ ≤
        2 * (T.d m : ℝ) ^ 9 ∧
      innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i ≤ 2 * j := by
  have hd1 : 1 ≤ (T.d m : ℝ) := (by norm_num : (1 : ℝ) ≤ 2).trans hd
  have hd0 : 0 < (T.d m : ℝ) := zero_lt_one.trans_le hd1
  have hi1 : (T.d m : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hd1
  have hA9 : morseChainA T m ≤ 9 :=
    (morseChainA_inv_bounds T m hd1).2.trans (by nlinarith only [hi1])
  have hB1 : morseChainB T m ≤ 1 := by
    rw [morseChainB_inv_pow T m hd0.le]
    simpa only [one_pow] using pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hi1 9
  have hp := morseChainParameters_pos T m hd
  have hm := innerMorseCapMass_bounds hp.2 hp.1 hA9 hB1 hj (decide (i ≠ 0))
  refine ⟨?_, hm.2⟩
  calc
    (innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i)⁻¹ ≤
        (morseChainB T m / 2)⁻¹ := by
      simpa only [one_div, innerMorseBufferMass] using one_div_le_one_div_of_le
        (div_pos hp.2 (by norm_num)) hm.1
    _ = 2 * (T.d m : ℝ) ^ 9 := by
      rw [morseChainB_inv_pow T m hd0.le, inv_pow, inv_div, div_eq_mul_inv, inv_inv]

theorem innerMorseBufferCoefficient_ge (T : MorseChainData) (m : ℕ)
    (hd : 1 ≤ (T.d m : ℝ)) : 16 ≤ innerMorseBufferCoefficient T m := by
  have hpow : 1 ≤ (T.d m : ℝ) ^ 9 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd 9
  simpa only [mul_one, innerMorseBufferCoefficient] using
    mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 16)

/-- All model inputs to the compression envelopes have the same raw
coefficient. The frequency factor is kept explicit. -/
theorem innerMorseChain_buffer_coefficient_bounds (T : MorseChainData) (m : ℕ)
    (hd : 2 ≤ (T.d m : ℝ)) {j : ℝ} (hj : 1 ≤ j) :
    let B := innerMorseBufferData (morseChainA T m) (morseChainB T m) j
      (8 * (T.d m : ℝ) ^ 9)
    let c := innerMorseBufferCoefficient T m
    1 ≤ c ∧ B.B₀ ≤ c ∧ B.layerBound ≤ c ∧
      (∀ i, (B.mass i)⁻¹ ≤ c) ∧ (∀ i, B.mass i ≤ c * (1 + j)) := by
  dsimp only
  have hd0 : 0 ≤ (T.d m : ℝ) := (by norm_num : (0 : ℝ) ≤ 2).trans hd
  have hc := innerMorseBufferCoefficient_ge T m ((by norm_num : (1 : ℝ) ≤ 2).trans hd)
  have hp : 0 ≤ (T.d m : ℝ) ^ 9 := pow_nonneg hd0 9
  refine ⟨(by norm_num : (1 : ℝ) ≤ 16).trans hc, ?_, ?_, ?_, ?_⟩
  · dsimp only [innerMorseBufferData, innerMorseBufferCoefficient]
    nlinarith only [hp]
  · exact (by norm_num : (4 : ℝ) ≤ 16).trans hc
  · intro i
    exact (innerMorseChain_buffer_mass_bounds T m hd hj i).1.trans
      (by dsimp only [innerMorseBufferCoefficient]; nlinarith only [hp])
  · intro i
    apply (innerMorseChain_buffer_mass_bounds T m hd hj i).2.trans
    have hj0 : 0 ≤ j := zero_le_one.trans hj
    have h2c : 2 ≤ innerMorseBufferCoefficient T m := (by norm_num : (2 : ℝ) ≤ 16).trans hc
    calc
      2 * j ≤ innerMorseBufferCoefficient T m * j := mul_le_mul_of_nonneg_right h2c hj0
      _ ≤ innerMorseBufferCoefficient T m * (1 + j) :=
        mul_le_mul_of_nonneg_left (by linarith) ((by norm_num : (0 : ℝ) ≤ 16).trans hc)

/-- The half-line inward energy dominates the mass. Its inverse square
root therefore fits in the same coefficient, without a mass≥1 premise. -/
theorem innerMorseChain_inverse_sqrt_energy_le (T : MorseChainData) (m : ℕ)
    (hd : 2 ≤ (T.d m : ℝ)) {j k : ℝ} (hj : 1 ≤ j) (i : Fin 2)
    (hk : innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i ≤ k) :
    (sqrt k)⁻¹ ≤ innerMorseBufferCoefficient T m := by
  have hp := morseChainParameters_pos T m hd
  have hm0 := innerMorseBufferMass_pos hp.2 hp.1 (zero_lt_one.trans_le hj) i
  have hk0 : 0 < k := hm0.trans_le hk
  have hi : k⁻¹ ≤ 2 * (T.d m : ℝ) ^ 9 := by
    apply (show k⁻¹ ≤
      (innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i)⁻¹ from ?_).trans
      (innerMorseChain_buffer_mass_bounds T m hd hj i).1
    simpa only [one_div] using one_div_le_one_div_of_le hm0 hk
  have hs : (sqrt k)⁻¹ ≤ 1 + k⁻¹ := by
    rw [← sqrt_inv k]
    apply sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [inv_nonneg.mpr hk0.le, sq_nonneg (k⁻¹)]
  have hd1 : 1 ≤ (T.d m : ℝ) ^ 9 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one
      ((by norm_num : (1 : ℝ) ≤ 2).trans hd) 9
  apply hs.trans
  dsimp only [innerMorseBufferCoefficient]
  nlinarith only [hi, hd1]

/-- The exponent nine is independent of the realization, chosen tail
and frequency. Local weight-ratio exponents can be added afterwards. -/
theorem innerMorseBufferCoefficient_le_weight (T : MorseChainData) (m : ℕ)
    (hd : T.d m = morseChainInteger m) :
    innerMorseBufferCoefficient T m ≤ (16 * (3 : ℝ) ^ 9) * radialE m ^ (9 : ℝ) := by
  have hE1 : 1 ≤ exp ((m : ℝ) ^ 2) := one_le_exp_iff.mpr (sq_nonneg _)
  have hdE : (T.d m : ℝ) ≤ 3 * exp ((m : ℝ) ^ 2) := by
    rw [hd]
    have h := morseChainInteger_lt m
    linarith only [h, hE1]
  have hEq : exp ((m : ℝ) ^ 2) ≤ radialE m := exp_le_exp.mpr (radial_nat_sq_le_Q m)
  have hdq : (T.d m : ℝ) ≤ 3 * radialE m :=
    hdE.trans (mul_le_mul_of_nonneg_left hEq (by norm_num))
  calc
    innerMorseBufferCoefficient T m ≤ 16 * (3 * radialE m) ^ 9 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hdq 9) (by norm_num)
    _ = (16 * (3 : ℝ) ^ 9) * radialE m ^ (9 : ℝ) := by
      rw [rpow_ofNat, mul_pow]
      ring

/-- This version accepts precisely the comparison exported by R09.
Its universal comparison constant only enlarges the coefficient factor,
and does not change the ninth coefficient exponent. -/
theorem innerMorseChain_inverse_sqrt_energy_le_scaled (T : MorseChainData) (m : ℕ)
    (hd : 2 ≤ (T.d m : ℝ)) {j k C : ℝ} (hj : 1 ≤ j) (hC : 0 < C) (i : Fin 2)
    (hk : innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i / C ≤ k) :
    (sqrt k)⁻¹ ≤ (1 + C) * innerMorseBufferCoefficient T m := by
  let mass := innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i
  have hp := morseChainParameters_pos T m hd
  have hm : 0 < mass := innerMorseBufferMass_pos hp.2 hp.1 (zero_lt_one.trans_le hj) i
  have hk0 : 0 < k := (div_pos hm hC).trans_le hk
  have hi : k⁻¹ ≤ C * mass⁻¹ := by
    have h := one_div_le_one_div_of_le (div_pos hm hC) hk
    calc
      k⁻¹ ≤ (mass / C)⁻¹ := by simpa only [one_div] using h
      _ = C * mass⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hi' : k⁻¹ ≤ C * (2 * (T.d m : ℝ) ^ 9) :=
    hi.trans (mul_le_mul_of_nonneg_left
      (innerMorseChain_buffer_mass_bounds T m hd hj i).1 hC.le)
  have hs : (sqrt k)⁻¹ ≤ 1 + k⁻¹ := by
    rw [← sqrt_inv k]
    exact sqrt_le_iff.mpr ⟨by positivity,
      by nlinarith only [inv_nonneg.mpr hk0.le, sq_nonneg (k⁻¹)]⟩
  have hd1 : 1 ≤ (T.d m : ℝ) ^ 9 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one
      ((by norm_num : (1 : ℝ) ≤ 2).trans hd) 9
  have hprod : 0 ≤ C * (T.d m : ℝ) ^ 9 :=
    mul_nonneg hC.le (pow_nonneg (Nat.cast_nonneg (T.d m)) 9)
  apply hs.trans
  dsimp only [innerMorseBufferCoefficient]
  nlinarith only [hi', hd1, hprod]

end ContinuousFlexibility.Radial
