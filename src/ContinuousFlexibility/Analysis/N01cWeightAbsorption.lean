import ContinuousFlexibility.Statements.Nonlinear

/-!
# A single constant for the coefficient and endpoint-weight estimates

After normalizing the material loss weight to be at least one, a raw
constant and exponent can be replaced by the same positive constant.
The height exponent is preserved exactly; no power of the height weight
is spent in this step.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Absorb the multiplier and the loss exponent into the same positive
constant, uniformly in the height weight and the nonnegative seminorm
factor.  No lower bound on the height weight is needed. -/
theorem exists_sameConstant_materialWeight_bound (C A γ : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ H E W : ℝ, 0 ≤ H → 1 ≤ E → 0 ≤ W →
      C * H ^ γ * E ^ A * W ≤ B * H ^ γ * E ^ B * W := by
  let B := max 1 (max C A)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB : 0 < B := zero_lt_one.trans_le hB1
  have hCB : C ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hAB : A ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hB, fun H E W hH hE hW => ?_⟩
  have hHγ : 0 ≤ H ^ γ := Real.rpow_nonneg hH γ
  have hEA : 0 ≤ E ^ A := Real.rpow_nonneg (zero_le_one.trans hE) A
  have hEB : E ^ A ≤ E ^ B :=
    Real.rpow_le_rpow_of_exponent_le hE hAB
  calc
    C * H ^ γ * E ^ A * W ≤ B * H ^ γ * E ^ A * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB hHγ) hEA) hW
    _ ≤ B * H ^ γ * E ^ B * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEB (mul_nonneg hB.le hHγ)) hW

end ContinuousFlexibility.Analysis
