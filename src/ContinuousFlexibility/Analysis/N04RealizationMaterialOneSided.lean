import ContinuousFlexibility.Analysis.MaterialSampleShift

/-!
# Exact height decay under a one-sided endpoint comparison

The sample coordinate may be much farther from the endpoint than the
evaluation coordinate. The cubic height decay absorbs the coefficient
weight in that region. When the coordinates are comparable, a bounded
height shift and a fixed coefficient rescaling retain the same height
exponent at the sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- A one-sided coordinate bound preserves every positive height exponent.
All constants precede both coordinates, including the zero coordinate. -/
theorem n04Realization_materialH_E0_rpow_oneSided
    {γ R L : ℝ} (hγ : 0 < γ) (hR : 0 ≤ R) (hL : 0 ≤ L) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ x y : ℝ,
      0 ≤ x → 0 ≤ y → y ≤ x + L →
      materialH x ^ γ * materialE0 x ^ R ≤
        B * materialH y ^ γ * materialE0 y ^ A := by
  obtain ⟨A₀, hA₀, hshift⟩ := materialH_neg_rpow_oneSided_shift hγ.le hL
  obtain ⟨C, hC, htail⟩ := materialH_rpow_mul_materialE0_rpow_le R
    (show 0 < 7 * γ / 8 by positivity)
  let A : ℝ := (A₀ + R) * ((2 : ℝ) ^ (5 / 2 : ℝ) * (Real.log 2 + 1))
  let B : ℝ := max 1 C
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B, A, zero_lt_one.trans_le hB, hA, fun x y hx hy hyx => ?_⟩
  have hHy : 0 ≤ materialH y ^ γ := Real.rpow_nonneg (materialH_pos y).le _
  have hEy : 1 ≤ materialE0 y ^ A := Real.one_le_rpow (materialE0_one_le hy) hA
  by_cases hnear : x ≤ 2 * y
  · have hheight : materialH x ^ γ ≤ materialH y ^ γ * materialE0 x ^ A₀ := by
      have h := hshift y x hy hx hyx
      simp only [materialH, materialE0, ← Real.exp_mul, ← Real.exp_add,
        Real.exp_le_exp] at h ⊢
      nlinarith only [h]
    have hcoefficient : materialE0 x ^ (A₀ + R) ≤ materialE0 y ^ A :=
      materialE0_rpow_scale_bound (C := (2 : ℝ)) (by norm_num) hy hx hnear
        (add_nonneg hA₀ hR)
    calc
      _ ≤ (materialH y ^ γ * materialE0 x ^ A₀) * materialE0 x ^ R :=
        mul_le_mul_of_nonneg_right hheight (Real.rpow_nonneg (materialE0_pos x).le _)
      _ = materialH y ^ γ * materialE0 x ^ (A₀ + R) := by
        rw [Real.rpow_add (materialE0_pos x)]
        ring
      _ ≤ materialH y ^ γ * materialE0 y ^ A :=
        mul_le_mul_of_nonneg_left hcoefficient hHy
      _ ≤ B * materialH y ^ γ * materialE0 y ^ A := by
        have h := mul_le_mul_of_nonneg_right hB
          (mul_nonneg hHy (Real.rpow_nonneg (materialE0_pos y).le A))
        simpa only [one_mul, mul_assoc] using h
  · have hcube : 8 * y ^ 3 ≤ x ^ 3 := by
      calc
        _ = (2 * y) ^ 3 := by ring
        _ ≤ x ^ 3 := pow_le_pow_left₀ (by positivity) (le_of_not_ge hnear) 3
    have hheight : materialH x ^ (γ / 8) ≤ materialH y ^ γ := by
      have h := mul_le_mul_of_nonneg_left hcube hγ.le
      simp only [materialH, ← Real.exp_mul, Real.exp_le_exp]
      nlinarith only [h]
    have hsplit : materialH x ^ γ =
        materialH x ^ (7 * γ / 8) * materialH x ^ (γ / 8) := by
      rw [← Real.rpow_add (materialH_pos x)]
      congr 1
      ring
    calc
      _ = (materialH x ^ (7 * γ / 8) * materialE0 x ^ R) *
          materialH x ^ (γ / 8) := by rw [hsplit]; ring
      _ ≤ C * materialH y ^ γ :=
        mul_le_mul (htail x hx) hheight
          (Real.rpow_nonneg (materialH_pos x).le _) hC.le
      _ ≤ B * materialH y ^ γ :=
        mul_le_mul_of_nonneg_right (le_max_right 1 C) hHy
      _ ≤ B * materialH y ^ γ * materialE0 y ^ A := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hEy
          (mul_nonneg (zero_le_one.trans hB) hHy)

end ContinuousFlexibility.Analysis
