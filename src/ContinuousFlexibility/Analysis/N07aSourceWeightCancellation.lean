import ContinuousFlexibility.Analysis.N07aVolumeCell

/-! # Exact cancellation of the actual integer material weights -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

theorem n07a_volumeWeight_inverse_nat {M H γ : ℝ} (hM : 0 < M) (hH : 0 < H)
    (t : ℕ) :
    (M ^ (-(t : ℝ)) * H ^ γ)⁻¹ * (H ^ γ * (M ^ (t + 2))⁻¹) = (M ^ 2)⁻¹ := by
  rw [Real.rpow_neg hM.le, Real.rpow_natCast, pow_add]
  field_simp [hM.ne', (Real.rpow_pos_of_pos hH γ).ne', pow_ne_zero t hM.ne']

theorem n07a_materialInverse_square_bound {x C B M : ℝ}
    (hx : 0 ≤ x) (hC : 0 ≤ C) (hB : 0 ≤ B) (hM : 1 ≤ M)
    (hbound : x ≤ C * M⁻¹ * B) :
    x ^ 2 ≤ M⁻¹ * (C * B) ^ 2 := by
  have hi0 : 0 ≤ M⁻¹ := inv_nonneg.mpr (zero_le_one.trans hM)
  have hi1 : M⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hM
  calc
    x ^ 2 ≤ (C * M⁻¹ * B) ^ 2 :=
      pow_le_pow_left₀ hx hbound 2
    _ = (M⁻¹) ^ 2 * (C * B) ^ 2 := by ring
    _ ≤ M⁻¹ * (C * B) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hi0, hi1]) (sq_nonneg _)

end ContinuousFlexibility.Analysis
