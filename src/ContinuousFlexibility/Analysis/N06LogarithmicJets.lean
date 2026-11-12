import ContinuousFlexibility.Analysis.N06PositiveClippedJets
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Actual logarithmic endpoint jets from primitive positive height data

The interpolation uses logarithms, but no logarithmic jet estimate needs
to be assumed separately: two ordinary height jets and a positive
reciprocal bound give the required polynomial estimate on each collar.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem N06ScalarJetTwoBound.log_at
    {f : ℝ → ℝ} {x B : ℝ} (hf : ContDiffAt ℝ ∞ f x)
    (hB : 1 ≤ B) (hfb : N06ScalarJetTwoBound f x B)
    (hpos : 0 < f x) (hinv : (f x)⁻¹ ≤ B) :
    N06ScalarJetTwoBound (fun t => Real.log (f t)) x (2 * B ^ 4) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hB14 : B ≤ B ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 4)
  have hB24 : B ^ 2 ≤ B ^ 4 := pow_le_pow_right₀ hB (by norm_num)
  have hB4 : 0 ≤ B ^ 4 := pow_nonneg hB0 _
  have hvalue : |Real.log (f x)| ≤ B := by
    apply abs_le.mpr
    constructor
    · have hi : Real.log ((f x)⁻¹) ≤ B :=
        (Real.log_le_self (inv_nonneg.mpr hpos.le)).trans hinv
      rw [Real.log_inv] at hi
      linarith
    · exact (Real.log_le_self hpos.le).trans
        ((le_abs_self _).trans hfb.value)
  have hd : deriv (fun t => Real.log (f t)) x = deriv f x * (f x)⁻¹ := by
    simpa only [div_eq_mul_inv] using
      ((hf.differentiableAt (by simp)).hasDerivAt.log hpos.ne').deriv
  have hdd : deriv (deriv (fun t => Real.log (f t))) x =
      -((f x) ^ 2)⁻¹ * deriv f x ^ 2 + (f x)⁻¹ * deriv (deriv f) x := by
    have he := iteratedDeriv_comp_two
      (Real.contDiffAt_log.mpr hpos.ne' : ContDiffAt ℝ 2 Real.log (f x))
      (hf.of_le (by simp))
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_zero, Function.comp_def, Real.deriv_log', deriv_inv] using he
  constructor
  · exact hvalue.trans (by nlinarith)
  · rw [hd, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
    have he := mul_le_mul hfb.first hinv (inv_nonneg.mpr hpos.le) hB0
    nlinarith
  · rw [hdd]
    have h₁ : |-((f x) ^ 2)⁻¹ * deriv f x ^ 2| ≤ B ^ 4 := by
      rw [abs_mul, abs_neg, ← inv_pow, abs_pow,
        abs_of_pos (inv_pos.mpr hpos), abs_pow]
      have he := mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hinv 2)
        (pow_le_pow_left₀ (abs_nonneg _) hfb.first 2) (sq_nonneg _) (sq_nonneg B)
      simpa only [← pow_add, show (2 + 2 : ℕ) = 4 from rfl] using he
    have h₂ : |(f x)⁻¹ * deriv (deriv f) x| ≤ B ^ 2 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
      simpa only [pow_two] using
        mul_le_mul hinv hfb.second (abs_nonneg _) hB0
    have he := (abs_add_le _ _).trans (add_le_add h₁ h₂)
    nlinarith

end ContinuousFlexibility.Analysis
