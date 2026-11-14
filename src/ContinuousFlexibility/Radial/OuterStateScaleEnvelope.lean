module

public import ContinuousFlexibility.Radial.OuterEnvelope
public import ContinuousFlexibility.Radial.MorseChainScales

/-!
# The reciprocal actual state scale fits the common envelope

The amplitude lower bound is uniform over the height cube. Together
with the permitted amplitude-to-state-scale ratio it gives one explicit
envelope exponent, independent of the frequency and all height choices.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

theorem outer_stateScale_inv_le (M : MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n : ℕ} (hn : 1 ≤ n)
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hscale : morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2)) :
    lam⁻¹ ≤ radialE n ^ (L + 1) := by
  let μ := morseChainAmplitude M σ n
  have hμ : 0 < μ := morseChainAmplitude_pos M σ hσ n
  have hμlower : exp (-(n : ℝ) ^ (5 / 2 : ℝ)) ≤ μ :=
    (morseChainAmplitude_bounds M σ hσ n).1
  have hμinv : μ⁻¹ ≤ exp ((n : ℝ) ^ (5 / 2 : ℝ)) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hμ).mpr
    calc
      1 = exp ((n : ℝ) ^ (5 / 2 : ℝ)) *
          exp (-(n : ℝ) ^ (5 / 2 : ℝ)) := by
        rw [← exp_add, add_neg_cancel, exp_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left hμlower (exp_pos _).le
  have hp : (n : ℝ) ^ (5 / 2 : ℝ) ≤ radialQ n := by
    exact le_mul_of_one_le_right (rpow_nonneg (Nat.cast_nonneg n) _)
      (ssv_one_le_log (Nat.cast_nonneg n))
  have hquad := mul_le_mul_of_nonneg_left (outer_nat_sq_le_radialQ hn) hL
  calc
    lam⁻¹ = (μ / lam) * μ⁻¹ := by field_simp [hμ.ne', hlam.ne'] <;> ring
    _ ≤ exp (L * (n : ℝ) ^ 2) * exp ((n : ℝ) ^ (5 / 2 : ℝ)) :=
      mul_le_mul hscale hμinv (inv_nonneg.mpr hμ.le) (exp_pos _).le
    _ = exp (L * (n : ℝ) ^ 2 + (n : ℝ) ^ (5 / 2 : ℝ)) := (exp_add _ _).symm
    _ ≤ exp ((L + 1) * radialQ n) := exp_le_exp.mpr (by linarith only [hquad, hp])
    _ = radialE n ^ (L + 1) := (outer_radialE_rpow n (L + 1)).symm

end ContinuousFlexibility.Radial
