import ContinuousFlexibility.Analysis.N04NegativeChartControlledCollar

/-! One material scale fixes the root flow before all state and spatial orders. -/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements

variable (W : N04RealizationStart)

def negativeChartRootScale (e : ℕ ≃ N04PieceIndex W.D) (C : ℝ)
    (m : ℕ) (side : Bool) : ℝ :=
  (1 / 2 : ℝ) * (1 + (W.negativeMaterialCollar m)⁻¹ +
    4 * C * W.T.E0 (W.negativeHalfSample e m side) ^ C)⁻¹

theorem negativeChartRootScale_bounds (e : ℕ ≃ N04PieceIndex W.D)
    {C : ℝ} (hC : 1 ≤ C) (m : ℕ) (side : Bool) :
    let δ := W.negativeChartRootScale e C m side
    0 < δ ∧ δ ≤ 1 ∧ δ * 2 ≤ W.negativeMaterialCollar m ∧
      δ ≤ W.negativeOpticalWidth m side ∧
      4 * δ * (C * W.T.E0 (W.negativeHalfSample e m side) ^ C) ≤ 1 := by
  let E := W.T.E0 (W.negativeHalfSample e m side)
  let D : ℝ := 1 + (W.negativeMaterialCollar m)⁻¹ + 4 * C * E ^ C
  have hc := W.negativeMaterialCollar_bounds m
  have hE : 1 ≤ E := W.floor _
  have hterm : 0 ≤ 4 * C * E ^ C := mul_nonneg
    (mul_nonneg (by norm_num) (zero_le_one.trans hC))
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith only [inv_pos.mpr hc.1, hterm]
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hδ : 0 < W.negativeChartRootScale e C m side :=
    mul_pos (by norm_num) (inv_pos.mpr hDp)
  have hδone : W.negativeChartRootScale e C m side ≤ 1 := by
    have hh := inv_le_one_of_one_le₀ hD
    change (1 / 2 : ℝ) * D⁻¹ ≤ 1
    linarith only [hh]
  have hcollar : W.negativeChartRootScale e C m side * 2 ≤ W.negativeMaterialCollar m := by
    have hh := inv_anti₀ (inv_pos.mpr hc.1)
      (show (W.negativeMaterialCollar m)⁻¹ ≤ D by dsimp only [D]; linarith only [hterm])
    rw [inv_inv] at hh
    change ((1 / 2 : ℝ) * D⁻¹) * 2 ≤ _
    linarith only [hh]
  refine ⟨hδ, hδone, hcollar, ?_, ?_⟩
  · have hh := hc.2.2.2 side
    linarith only [hδ, hcollar, hh]
  · have htermD : 4 * C * E ^ C ≤ D := by
      dsimp only [D]
      linarith only [inv_pos.mpr hc.1]
    have hh := mul_le_mul_of_nonneg_right htermD (inv_pos.mpr hDp).le
    rw [mul_inv_cancel₀ hDp.ne'] at hh
    change 4 * ((1 / 2 : ℝ) * D⁻¹) * (C * E ^ C) ≤ 1
    nlinarith only [hh]

theorem negativeChartRootScale_inverse_material
    (e : ℕ ≃ N04PieceIndex W.D) {C : ℝ} (hC : 1 ≤ C) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side,
      (W.negativeChartRootScale e C m side)⁻¹ ≤
        B * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  obtain ⟨B, A, hB, hA, hb⟩ := W.negativeMaterialCollar_inverse_material e
  have hCpos := zero_lt_one.trans_le hC
  refine ⟨2 * (1 + B + 4 * C), A + C, by positivity, add_nonneg hA hCpos.le,
    fun m side => ?_⟩
  let E := W.T.E0 (W.negativeHalfSample e m side)
  have hE : 1 ≤ E := W.floor _
  have h₁ := Real.one_le_rpow hE (add_nonneg hA hCpos.le)
  have h₂ := (hb m side).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hCpos.le)) hB.le)
  have h₃ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hA))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCpos.le)
  have hs := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h₁ h₂) h₃)
    (by norm_num : (0 : ℝ) ≤ 2)
  simp only [negativeChartRootScale, mul_inv_rev, inv_inv, inv_div, inv_one,
    div_one]
  convert hs using 1 <;> ring

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeChartRootScale_inverse_material'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeChartRootScale_inverse_material
