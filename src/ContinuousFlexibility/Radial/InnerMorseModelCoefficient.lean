module

public import ContinuousFlexibility.Radial.InnerMorseCompressionConstruction

/-!
# One Morse coefficient including both weight ratios

The integer coefficient alone does not dominate the adjacent weight
ratio. The common coefficient below includes the ninth power of E_m,
as well as the universal R09 comparison constant. It controls the raw
model costs, the actual whole-cell velocity, both cut weight ratios,
and the inverse square root of the inward energy. Its eighth power
still fits the fixed exponent eighty used in the ordered choices.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

def innerMorseModelCoefficientConstant (C : ℝ) : ℝ :=
  (2 + C) * (16 * (3 : ℝ) ^ 9)

def innerMorseModelCoefficient (C : ℝ) (m : ℕ) : ℝ :=
  innerMorseModelCoefficientConstant C * radialE m ^ 9

theorem innerMorseModelCoefficientConstant_ge {C : ℝ} (hC : 0 ≤ C) :
    16 ≤ innerMorseModelCoefficientConstant C := by
  have hfac : (1 : ℝ) ≤ 2 + C := by linarith only [hC]
  calc
    16 ≤ 16 * (3 : ℝ) ^ 9 := by norm_num
    _ ≤ (2 + C) * (16 * (3 : ℝ) ^ 9) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac
        (by norm_num : (0 : ℝ) ≤ 16 * (3 : ℝ) ^ 9)
    _ = innerMorseModelCoefficientConstant C := rfl

theorem innerMorseModelCoefficient_base {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    16 ≤ innerMorseModelCoefficient C m ∧ radialE m ≤ innerMorseModelCoefficient C m := by
  have hE : 1 ≤ radialE m := one_le_exp_iff.mpr (radialQ_nonneg m)
  have hconst := innerMorseModelCoefficientConstant_ge hC
  have hconst0 : 0 ≤ innerMorseModelCoefficientConstant C :=
    (by norm_num : (0 : ℝ) ≤ 16).trans hconst
  have hconst1 : 1 ≤ innerMorseModelCoefficientConstant C :=
    (by norm_num : (1 : ℝ) ≤ 16).trans hconst
  constructor
  · exact hconst.trans (by
      simpa only [innerMorseModelCoefficient, mul_one] using
        mul_le_mul_of_nonneg_left (one_le_pow₀ hE : (1 : ℝ) ≤ radialE m ^ 9) hconst0)
  · have hp : radialE m ≤ radialE m ^ 9 := by
      simpa only [pow_one] using pow_le_pow_right₀ hE (by norm_num : 1 ≤ 9)
    exact hp.trans (by
      simpa only [innerMorseModelCoefficient, one_mul] using
        mul_le_mul_of_nonneg_right hconst1 (pow_nonneg (zero_le_one.trans hE) 9))

theorem innerMorseModelCoefficient_raw {T : MorseChainData} {m : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hd : T.d m = morseChainInteger m) :
    innerMorseBufferCoefficient T m ≤ innerMorseModelCoefficient C m ∧
      (1 + C) * innerMorseBufferCoefficient T m ≤ innerMorseModelCoefficient C m := by
  have hE0 : 0 ≤ radialE m := (exp_pos _).le
  have hraw : innerMorseBufferCoefficient T m ≤
      (16 * (3 : ℝ) ^ 9) * radialE m ^ 9 := by
    simpa only [rpow_ofNat] using innerMorseBufferCoefficient_le_weight T m hd
  have hbase0 : 0 ≤ (16 * (3 : ℝ) ^ 9) * radialE m ^ 9 := by positivity
  have hbase : (16 * (3 : ℝ) ^ 9) * radialE m ^ 9 ≤ innerMorseModelCoefficient C m := by
    calc
      _ ≤ (2 + C) * ((16 * (3 : ℝ) ^ 9) * radialE m ^ 9) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (show (1 : ℝ) ≤ 2 + C by linarith only [hC]) hbase0
      _ = _ := by unfold innerMorseModelCoefficient innerMorseModelCoefficientConstant; ring
  refine ⟨hraw.trans hbase, ?_⟩
  calc
    _ ≤ (1 + C) * ((16 * (3 : ℝ) ^ 9) * radialE m ^ 9) :=
      mul_le_mul_of_nonneg_left hraw (by linarith only [hC])
    _ ≤ (2 + C) * ((16 * (3 : ℝ) ^ 9) * radialE m ^ 9) :=
      mul_le_mul_of_nonneg_right (by linarith) hbase0
    _ = _ := by unfold innerMorseModelCoefficient innerMorseModelCoefficientConstant; ring

/-- All scalar input bounds for the true physical remainder, including
the weight ratio E_m, use the same enlarged coefficient. -/
theorem innerMorseModelCoefficient_bounds (T : MorseChainData) (m : ℕ)
    (hd : T.d m = morseChainInteger m) {C j : ℝ} (hC : 0 ≤ C) (hj : 1 ≤ j) :
    let B := innerMorseBufferData (morseChainA T m) (morseChainB T m) j
      (8 * (T.d m : ℝ) ^ 9)
    let c := innerMorseModelCoefficient C m
    1 ≤ c ∧ B.B₀ ≤ c ∧ B.layerBound ≤ c ∧
      (∀ i, (B.mass i)⁻¹ ≤ c) ∧ (∀ i, B.mass i ≤ c * (1 + j)) ∧
      14 ≤ c ∧ radialE m ≤ c := by
  dsimp only
  have hd2 : 2 ≤ (T.d m : ℝ) := by
    rw [hd]
    exact_mod_cast morseChainInteger_ge_two m
  have hc := innerMorseChain_buffer_coefficient_bounds T m hd2 hj
  have hraw := (innerMorseModelCoefficient_raw hC hd).1
  have hbase := innerMorseModelCoefficient_base hC m
  refine ⟨hc.1.trans hraw, hc.2.1.trans hraw, hc.2.2.1.trans hraw,
    (fun i => (hc.2.2.2.1 i).trans hraw), ?_,
    (by norm_num : (14 : ℝ) ≤ 16).trans hbase.1, hbase.2⟩
  intro i
  exact (hc.2.2.2.2 i).trans (mul_le_mul_of_nonneg_right hraw (by linarith only [hj]))

theorem innerMorseModelCoefficient_inverse_sqrt_energy (T : MorseChainData) (m : ℕ)
    (hd : T.d m = morseChainInteger m) {C j k : ℝ} (hC : 0 < C) (hj : 1 ≤ j)
    (i : Fin 2)
    (hk : innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i / C ≤ k) :
    (sqrt k)⁻¹ ≤ innerMorseModelCoefficient C m := by
  have hd2 : 2 ≤ (T.d m : ℝ) := by
    rw [hd]
    exact_mod_cast morseChainInteger_ge_two m
  exact (innerMorseChain_inverse_sqrt_energy_le_scaled T m hd2 hj hC i hk).trans
    (innerMorseModelCoefficient_raw hC.le hd).2

/-- Coefficient powers through eight fit the single preselected
exponent eighty. The amplitude remains free to absorb fixed constants. -/
theorem innerMorseModelCoefficient_pow_le {C H A : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hA : H * innerMorseModelCoefficientConstant C ^ 8 ≤ A)
    (m : ℕ) {k : ℕ} (hk : k ≤ 8) :
    H * innerMorseModelCoefficient C m ^ k ≤ A * radialE m ^ (80 : ℝ) := by
  have hE : 1 ≤ radialE m := one_le_exp_iff.mpr (radialQ_nonneg m)
  have hE0 : 0 ≤ radialE m := zero_le_one.trans hE
  have hc1 : 1 ≤ innerMorseModelCoefficient C m :=
    (by norm_num : (1 : ℝ) ≤ 16).trans (innerMorseModelCoefficient_base hC m).1
  have hA0 : 0 ≤ A := (mul_nonneg hH (pow_nonneg
    ((by norm_num : (0 : ℝ) ≤ 16).trans (innerMorseModelCoefficientConstant_ge hC)) 8)).trans hA
  have hpower : radialE m ^ 72 ≤ radialE m ^ 80 :=
    pow_le_pow_right₀ hE (by norm_num)
  calc
    _ ≤ H * innerMorseModelCoefficient C m ^ 8 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc1 hk) hH
    _ = (H * innerMorseModelCoefficientConstant C ^ 8) * radialE m ^ 72 := by
      rw [innerMorseModelCoefficient, mul_pow, ← pow_mul]
      ring
    _ ≤ A * radialE m ^ 80 := mul_le_mul hA hpower (pow_nonneg hE0 72) hA0
    _ = A * radialE m ^ (80 : ℝ) := by rw [rpow_ofNat]

end ContinuousFlexibility.Radial
