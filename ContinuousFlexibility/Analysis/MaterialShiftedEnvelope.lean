import ContinuousFlexibility.Analysis.MaterialWeights

/-!
# Comparing endpoint weights at distinct sample locations

The cubic exponent in H dominates the E0 loss when the sample locations
are comparable to the endpoint coordinate. This is the estimate needed
when the amplitude and the control derivatives use different cell samples.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

theorem material_shifted_envelope {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y z : ℝ, 0 ≤ x → x / 2 ≤ y →
      0 ≤ z → z ≤ 2 * x →
      materialH y ^ γ * materialE0 z ^ A ≤ K * materialH x ^ (γ / 16) := by
  have hε : 0 < γ / 128 := div_pos hγ (by norm_num)
  obtain ⟨K, hK, hb⟩ := materialH_rpow_mul_materialE0_rpow_le A hε
  refine ⟨K, hK, fun x y z hx hy hz hz' => ?_⟩
  have hp : 0 < materialH z ^ (γ / 128) := Real.rpow_pos_of_pos (materialH_pos z) _
  have hratio : materialH y ^ γ / materialH z ^ (γ / 128) ≤ materialH x ^ (γ / 16) := by
    simp only [materialH, ← Real.exp_mul, ← Real.exp_sub, Real.exp_le_exp]
    have hy3 : (x / 2) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by positivity) hy 3
    have hz3 : z ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ hz hz' 3
    nlinarith only [mul_le_mul_of_nonneg_left hy3 hγ.le, mul_le_mul_of_nonneg_left hz3 hε.le]
  calc
    materialH y ^ γ * materialE0 z ^ A =
        (materialH y ^ γ / materialH z ^ (γ / 128)) *
          (materialH z ^ (γ / 128) * materialE0 z ^ A) := by
      field_simp [hp.ne']
    _ ≤ (materialH y ^ γ / materialH z ^ (γ / 128)) * K :=
      mul_le_mul_of_nonneg_left (hb z hz)
        (div_nonneg (Real.rpow_pos_of_pos (materialH_pos y) _).le hp.le)
    _ ≤ materialH x ^ (γ / 16) * K := mul_le_mul_of_nonneg_right hratio hK.le
    _ = K * materialH x ^ (γ / 16) := mul_comm _ _

theorem material_bounded_shift_envelope {γ : ℝ} (hγ : 0 < γ) (A : ℝ)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y z : ℝ, 2 * C ≤ x → |y - x| ≤ C →
      |z - x| ≤ C → 0 ≤ z →
      materialH y ^ γ * materialE0 z ^ A ≤ K * materialH x ^ (γ / 16) := by
  obtain ⟨K, hK, hb⟩ := material_shifted_envelope hγ A
  refine ⟨K, hK, fun x y z hx hy hz hz' => hb x y z ?_ ?_ hz' ?_⟩
  · linarith
  · have h := (abs_le.mp hy).1
    linarith
  · have h := (abs_le.mp hz).2
    linarith

end ContinuousFlexibility.Analysis
