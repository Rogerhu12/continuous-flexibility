module

public import ContinuousFlexibility.Analysis.N05TwoWeightBlocks

/-!
# The same two physical endpoint bounds control every inner exponent

The final canonical estimate uses three exponents strictly inside the two
physical endpoint bounds. Moving the conjugating exponent away from their
midpoint consumes only the corresponding part of the off-diagonal decay.
The physical inverse and its two endpoint estimates stay fixed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

theorem n05_innerExponent_block_bound
    (Sk Sm Qk Qm β γ ε δ M0 M1 C x y : ℝ)
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hγ : |γ - β| ≤ δ)
    (hmid : Real.exp (β * (Sk - Sm)) * y ≤
      C * Real.exp (M1 * Qk + M0 * Qm - ε * |Sk - Sm|) * x) :
    Real.exp (γ * (Sk - Sm)) * y ≤
      C * Real.exp (M1 * Qk + M0 * Qm - (ε - δ) * |Sk - Sm|) * x := by
  have hshift : (γ - β) * (Sk - Sm) ≤ δ * |Sk - Sm| := by
    calc
      _ ≤ |(γ - β) * (Sk - Sm)| := le_abs_self _
      _ = |γ - β| * |Sk - Sm| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hγ (abs_nonneg _)
  calc
    _ = Real.exp ((γ - β) * (Sk - Sm)) *
        (Real.exp (β * (Sk - Sm)) * y) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp ((γ - β) * (Sk - Sm)) *
        (C * Real.exp (M1 * Qk + M0 * Qm - ε * |Sk - Sm|) * x) :=
      mul_le_mul_of_nonneg_left hmid (Real.exp_pos _).le
    _ = C * Real.exp ((γ - β) * (Sk - Sm) +
        (M1 * Qk + M0 * Qm - ε * |Sk - Sm|)) * x := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hshift])) hC) hx

end ContinuousFlexibility.Analysis
