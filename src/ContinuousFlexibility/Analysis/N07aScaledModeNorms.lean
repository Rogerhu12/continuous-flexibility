module

public import ContinuousFlexibility.Analysis.N07aModeProductBounds

/-!
# The exact interval-length factors in the principal block estimate

The second derivative and first derivative in the mode energy are the
affine normalizations of the original weak derivatives. These seven
bounds keep that normalization when the cubic coefficient is restored.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

def n07aScaledModeEnergy (ℓ j : ℝ) (u d dd : N07aIntervalL2) : ℝ :=
  n07aCylinderEnergy j u (ℓ • d) (ℓ ^ 2 • dd)

theorem n07a_scaledMode_norm_bounds {ℓ j : ℝ} (hℓ : 0 < ℓ) (hj : 0 ≤ j)
    (u d dd : N07aIntervalL2) :
    ℓ ^ 6 * ‖n07aCylinderPower 3 dd‖ ≤ ℓ ^ 4 * Real.sqrt (n07aScaledModeEnergy ℓ j u d dd) ∧
    ℓ ^ 5 * ‖n07aCylinderPower 2 d‖ ≤ ℓ ^ 4 * Real.sqrt (n07aScaledModeEnergy ℓ j u d dd) ∧
    j * ℓ ^ 6 * ‖n07aCylinderPower 3 d‖ ≤ ℓ ^ 5 * Real.sqrt (n07aScaledModeEnergy ℓ j u d dd) ∧
    j * ℓ ^ 5 * ‖n07aCylinderPower 2 u‖ ≤ ℓ ^ 5 * Real.sqrt (n07aScaledModeEnergy ℓ j u d dd) ∧
    j ^ 2 * ℓ ^ 6 * ‖n07aCylinderPower 3 u‖ ≤ ℓ ^ 6 * Real.sqrt (n07aScaledModeEnergy ℓ j u d dd) ∧
    ℓ ^ 6 * ‖n07aCylinderPower 3 d‖ ≤ ℓ ^ 5 * Real.sqrt (n07aScaledModeEnergy ℓ j u d dd) ∧
    j * ℓ ^ 6 * ‖n07aCylinderPower 3 u‖ ≤ ℓ ^ 6 * Real.sqrt (n07aScaledModeEnergy ℓ j u d dd) := by
  let E := Real.sqrt (n07aScaledModeEnergy ℓ j u d dd)
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := n07aCylinderEnergy_root_norms j u (ℓ • d) (ℓ ^ 2 • dd)
  simp only [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hℓ, abs_of_nonneg (sq_nonneg ℓ)] at h₀ h₁ h₂
  have h₅ : ℓ * ‖n07aCylinderPower 3 d‖ ≤ E :=
    (mul_le_mul_of_nonneg_left (n07aCylinderPower_norm_antitone (by norm_num : 2 ≤ 3) d) hℓ.le).trans h₁
  have h₆ : j * ‖n07aCylinderPower 3 u‖ ≤ E :=
    (mul_le_mul_of_nonneg_left (n07aCylinderPower_norm_antitone (by norm_num : 2 ≤ 3) u) hj).trans h₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left h₀ (pow_nonneg hℓ.le 4)
    convert h using 1 <;> first | rfl | ring
  · have h := mul_le_mul_of_nonneg_left h₁ (pow_nonneg hℓ.le 4)
    convert h using 1 <;> first | rfl | ring
  · have h := mul_le_mul_of_nonneg_left h₂ (pow_nonneg hℓ.le 5)
    convert h using 1 <;> first | rfl | ring
  · have h := mul_le_mul_of_nonneg_left h₃ (pow_nonneg hℓ.le 5)
    convert h using 1 <;> first | rfl | ring
  · have h := mul_le_mul_of_nonneg_left h₄ (pow_nonneg hℓ.le 6)
    convert h using 1 <;> first | rfl | ring
  · have h := mul_le_mul_of_nonneg_left h₅ (pow_nonneg hℓ.le 5)
    convert h using 1 <;> first | rfl | ring
  · have h := mul_le_mul_of_nonneg_left h₆ (pow_nonneg hℓ.le 6)
    convert h using 1 <;> first | rfl | ring

theorem n07a_scaledMode_principal_budget {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    5 * ℓ ^ 4 + 7 * ℓ ^ 5 + 2 * ℓ ^ 6 ≤ 14 * (1 + ℓ) ^ 6 := by
  have h₄ : ℓ ^ 4 ≤ (1 + ℓ) ^ 6 :=
    (pow_le_pow_left₀ hℓ (by linarith) 4).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + ℓ) (by norm_num : 4 ≤ 6))
  have h₅ : ℓ ^ 5 ≤ (1 + ℓ) ^ 6 :=
    (pow_le_pow_left₀ hℓ (by linarith) 5).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + ℓ) (by norm_num : 5 ≤ 6))
  have h₆ : ℓ ^ 6 ≤ (1 + ℓ) ^ 6 := pow_le_pow_left₀ hℓ (by linarith) 6
  linarith

end ContinuousFlexibility.Analysis
