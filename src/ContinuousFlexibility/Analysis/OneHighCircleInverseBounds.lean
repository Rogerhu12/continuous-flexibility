import ContinuousFlexibility.Analysis.OneHighCircleInverseGeometry
import Mathlib.Tactic.Positivity

/-!
# Uniform low geometry of the genuine inverse lift

Only the first three forward derivatives and the positive lower bound for
the first derivative enter these constants. In particular no fourth-derivative
supremum is assumed. The low inverse Sobolev estimate can then use composition
of the reciprocal defect and the genuine change-of-variables estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

def circleInverseLowBound (c B : ℝ) : ℝ :=
  max 1 (max c⁻¹ (max (B * (c⁻¹) ^ 3)
    (3 * B ^ 2 * (c⁻¹) ^ 5 + B * (c⁻¹) ^ 4)))

theorem circleInverseLowBound_one_le (c B : ℝ) : 1 ≤ circleInverseLowBound c B :=
  le_max_left _ _

theorem circleInverseLowBound_nonneg (c B : ℝ) : 0 ≤ circleInverseLowBound c B :=
  zero_le_one.trans (circleInverseLowBound_one_le c B)

theorem circleInverse_deriv_lower {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
    (hι : ∀ x, h (ι x) = x) {c B : ℝ} (hc : 0 < c)
    (hlower : ∀ x, c ≤ deriv h x) (hupper : ∀ x, deriv h x ≤ B) (x : ℝ) :
    B⁻¹ ≤ deriv ι x := by
  have hd : 0 < deriv h (ι x) := hc.trans_le (hlower (ι x))
  rw [circleInverse_deriv hh hi hι x hd.ne']
  simpa only [one_div] using one_div_le_one_div_of_le hd (hupper (ι x))

theorem circleInverse_deriv_norm_le {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
    (hι : ∀ x, h (ι x) = x) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x, c ≤ deriv h x) (x : ℝ) : ‖deriv ι x‖ ≤ c⁻¹ := by
  have hd : 0 < deriv h (ι x) := hc.trans_le (hlower (ι x))
  rw [circleInverse_deriv hh hi hι x hd.ne', Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  simpa only [one_div] using one_div_le_one_div_of_le hc (hlower (ι x))

theorem circleInverse_second_norm_le {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
    (hι : ∀ x, h (ι x) = x) {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hlower : ∀ x, c ≤ deriv h x)
    (hsecond : ∀ x, ‖iteratedDeriv 2 h x‖ ≤ B) (x : ℝ) :
    ‖iteratedDeriv 2 ι x‖ ≤ B * (c⁻¹) ^ 3 := by
  have hd : 0 < deriv h (ι x) := hc.trans_le (hlower (ι x))
  have hinv : (deriv h (ι x))⁻¹ ≤ c⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hc (hlower (ι x))
  rw [circleInverse_iteratedDeriv_two hh hi hι x hd.ne', norm_mul, norm_neg,
    norm_pow, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  exact mul_le_mul (hsecond (ι x))
    (pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 3) (by positivity) hB

theorem circleInverse_third_norm_le {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
    (hι : ∀ x, h (ι x) = x) {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hlower : ∀ x, c ≤ deriv h x)
    (hsecond : ∀ x, ‖iteratedDeriv 2 h x‖ ≤ B)
    (hthird : ∀ x, ‖iteratedDeriv 3 h x‖ ≤ B) (x : ℝ) :
    ‖iteratedDeriv 3 ι x‖ ≤ 3 * B ^ 2 * (c⁻¹) ^ 5 + B * (c⁻¹) ^ 4 := by
  have hd : 0 < deriv h (ι x) := hc.trans_le (hlower (ι x))
  have hinv : (deriv h (ι x))⁻¹ ≤ c⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hc (hlower (ι x))
  have hfirstTerm : 3 * ‖iteratedDeriv 2 h (ι x)‖ ^ 2 * ((deriv h (ι x))⁻¹) ^ 5 ≤
      3 * B ^ 2 * (c⁻¹) ^ 5 :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hsecond (ι x)) 2)
        (by norm_num : (0 : ℝ) ≤ 3))
      (pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 5) (by positivity) (by positivity)
  have hsecondTerm : ‖iteratedDeriv 3 h (ι x)‖ * ((deriv h (ι x))⁻¹) ^ 4 ≤
      B * (c⁻¹) ^ 4 :=
    mul_le_mul (hthird (ι x)) (pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 4)
      (by positivity) hB
  rw [circleInverse_iteratedDeriv_three hh hi hι x hd.ne']
  calc
    _ ≤ ‖3 * (iteratedDeriv 2 h (ι x)) ^ 2 * ((deriv h (ι x))⁻¹) ^ 5‖ +
        ‖iteratedDeriv 3 h (ι x) * ((deriv h (ι x))⁻¹) ^ 4‖ := norm_sub_le _ _
    _ = 3 * ‖iteratedDeriv 2 h (ι x)‖ ^ 2 * ((deriv h (ι x))⁻¹) ^ 5 +
        ‖iteratedDeriv 3 h (ι x)‖ * ((deriv h (ι x))⁻¹) ^ 4 := by
      simp only [norm_mul, norm_pow, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
      norm_num
    _ ≤ _ := add_le_add hfirstTerm hsecondTerm

/-- One bound for every low inverse derivative, derived from the actual
inverse relation and the prescribed forward geometry. -/
theorem circleInverse_iteratedDeriv_norm_le {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
    (hι : ∀ x, h (ι x) = x) {c B : ℝ} (hc : 0 < c) (hB : 1 ≤ B)
    (hlower : ∀ x, c ≤ deriv h x)
    (hbound : ∀ j, 1 ≤ j → j ≤ 3 → ∀ x, ‖iteratedDeriv j h x‖ ≤ B)
    {j : ℕ} (hj : 1 ≤ j) (hj3 : j ≤ 3) (x : ℝ) :
    ‖iteratedDeriv j ι x‖ ≤ circleInverseLowBound c B := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · rw [iteratedDeriv_one]
    exact (circleInverse_deriv_norm_le hh hi hι hc hlower x).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (circleInverse_second_norm_le hh hi hι hc hB0 hlower
      (hbound 2 (by omega) (by omega)) x).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · exact (circleInverse_third_norm_le hh hi hι hc hB0 hlower
      (hbound 2 (by omega) (by omega)) (hbound 3 (by omega) (by omega)) x).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

end ContinuousFlexibility.Analysis
