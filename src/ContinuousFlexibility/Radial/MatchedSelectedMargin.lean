import ContinuousFlexibility.Radial.R07UniformSelection
import ContinuousFlexibility.Radial.MorseChainScales

/-!
# The actual first and later matching margins have one reciprocal bound

The first margin is fixed before the modal frequency. The later margin
is the selected tolerance times exp(-n²)/8. The same positive constant
therefore bounds both reciprocal costs by exp(radialQ n).
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

def matchedSelectedMarginConstant (η Cstar : ℝ) : ℝ :=
  4 / η + 32 / r07UniformTolerance Cstar + 2

theorem matchedSelectedMarginConstant_pos {η Cstar : ℝ}
    (hη : 0 < η) (hCstar : 0 ≤ Cstar) :
    0 < matchedSelectedMarginConstant η Cstar := by
  have hτ := r07UniformTolerance_pos hCstar
  unfold matchedSelectedMarginConstant
  positivity

/-- This covers exactly the two margins returned by the actual selected
regional constructor; the constant is independent of n and of frequency. -/
theorem matchedSelectedMargin_bound {η Cstar δ : ℝ}
    (hη : 0 < η) (hCstar : 0 ≤ Cstar) (n : ℕ)
    (hδ : δ = η ∨ δ = r07UniformTolerance Cstar * exp (-(n : ℝ) ^ 2) / 8) :
    4 / δ + 1 ≤ matchedSelectedMarginConstant η Cstar * exp (radialQ n) := by
  have hτ := r07UniformTolerance_pos hCstar
  have ha : 0 ≤ 4 / η := div_nonneg (by norm_num) hη.le
  have hb : 0 ≤ 32 / r07UniformTolerance Cstar :=
    div_nonneg (by norm_num) hτ.le
  have hconst := matchedSelectedMarginConstant_pos hη hCstar
  have hE : 1 ≤ exp (radialQ n) :=
    one_le_exp_iff.mpr ((sq_nonneg (n : ℝ)).trans (radial_nat_sq_le_Q n))
  rcases hδ with hfirst | hlater
  · rw [hfirst]
    calc
      _ ≤ matchedSelectedMarginConstant η Cstar := by
        unfold matchedSelectedMarginConstant
        linarith only [hb]
      _ = matchedSelectedMarginConstant η Cstar * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hE hconst.le
  · rw [hlater]
    have hreciprocal :
        4 / (r07UniformTolerance Cstar * exp (-(n : ℝ) ^ 2) / 8) =
          (32 / r07UniformTolerance Cstar) * exp ((n : ℝ) ^ 2) := by
      rw [exp_neg]
      field_simp [ne_of_gt hτ, exp_ne_zero] <;> ring
    rw [hreciprocal]
    calc
      _ ≤ (32 / r07UniformTolerance Cstar) * exp (radialQ n) + exp (radialQ n) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (exp_le_exp.mpr (radial_nat_sq_le_Q n)) hb) hE
      _ = (32 / r07UniformTolerance Cstar + 1) * exp (radialQ n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        unfold matchedSelectedMarginConstant
        linarith only [ha]) (exp_pos _).le

end ContinuousFlexibility.Radial
