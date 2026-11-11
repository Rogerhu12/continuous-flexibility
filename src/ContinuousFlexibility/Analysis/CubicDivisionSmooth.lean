import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.SmoothScaledIntegral
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Smooth division by a cubic zero

Taylor's formula on the segment from `0` to `y` identifies the quotient with
an integral on the fixed interval `[0, 1]`. The formula holds for every real
`y`, including negative values; its value at zero agrees with the prescribed
third derivative divided by six. Smooth parameter integration then gives a
global smooth extension, which can be used in the one-dimensional Hardy
estimate without any endpoint extension assumptions.

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex`, the paragraph
"The difference vanishes to third order at the roots".
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff Interval

private theorem integral_one_sub_sq :
    (∫ t in (0 : ℝ)..1, (1 - t) ^ 2) = 1 / 3 := by
  calc
    (∫ t in (0 : ℝ)..1, (1 - t) ^ 2) = ∫ t in (0 : ℝ)..1, t ^ 2 := by
      simpa only [one_mul, inv_one, one_smul, sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_mul (fun t : ℝ => t ^ 2)
          (a := 0) (b := 1) (c := 1) one_ne_zero (1 : ℝ))
    _ = 1 / 3 := by norm_num

/-- Taylor's remainder after the first three vanishing coefficients, with
the radial power pulled outside the integral. -/
theorem cubic_taylor_integral {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (hf2 : iteratedDeriv 2 f 0 = 0)
    (y : ℝ) :
    f y = y ^ 3 * ((1 / 2 : ℝ) *
      ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * iteratedDeriv 3 f (t * y)) := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := (0 : ℝ)) (y := y) (n := 2)
    (fun t _ => hf.contDiffAt.of_le (by norm_num))
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, zero_add] at ht
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    hf0, hf1, hf2] at ht
  have hpull :
      (∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * (y ^ 3 * iteratedDeriv 3 f (t * y))) =
        y ^ 3 * ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * iteratedDeriv 3 f (t * y) := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          y ^ 3 * ((1 - t) ^ 2 * iteratedDeriv 3 f (t * y)) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hpull] at ht
  calc
    f y = (1 / 2 : ℝ) *
        (y ^ 3 * ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * iteratedDeriv 3 f (t * y)) := ht
    _ = _ := by ring

/-- The prescribed value at zero is exactly the value of the smooth
Taylor integral, so this identity holds on the whole real line. -/
theorem cubicQuotient_eq_integral {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (hf2 : iteratedDeriv 2 f 0 = 0)
    (y : ℝ) :
    cubicQuotient f y = (1 / 2 : ℝ) *
      ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * iteratedDeriv 3 f (t * y) := by
  by_cases hy : y = 0
  · subst y
    simp only [cubicQuotient, ↓reduceIte, mul_zero]
    rw [intervalIntegral.integral_mul_const, integral_one_sub_sq]
    ring
  · rw [cubicQuotient, ite_eq_right hy]
    apply (div_eq_iff (pow_ne_zero 3 hy)).mpr
    exact (cubic_taylor_integral hf hf0 hf1 hf2 y).trans (mul_comm _ _)

/-- Multiplication restores the original function, including at the
removable singularity. This algebraic identity only uses its zero value. -/
theorem cube_mul_cubicQuotient {f : ℝ → ℝ} (hf0 : f 0 = 0) (y : ℝ) :
    y ^ 3 * cubicQuotient f y = f y := by
  by_cases hy : y = 0
  · subst y
    simp only [zero_pow (by decide : 3 ≠ 0), zero_mul, hf0]
  · rw [cubicQuotient, ite_eq_right hy, mul_comm]
    exact div_mul_cancel₀ (f y) (pow_ne_zero 3 hy)

/-- A smooth function vanishing with its first two derivatives at zero
has the prescribed globally smooth cubic quotient. -/
theorem contDiff_cubicQuotient {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (hf2 : iteratedDeriv 2 f 0 = 0) :
    ContDiff ℝ ∞ (cubicQuotient f) := by
  have hf3 : ContDiff ℝ ∞ (iteratedDeriv 3 f) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv 3 hf
  have hw : Continuous (fun t : ℝ => (1 - t) ^ 2) :=
    (continuous_const.sub continuous_id).pow 2
  have heq : cubicQuotient f = fun y => (1 / 2 : ℝ) *
      ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * iteratedDeriv 3 f (t * y) :=
    funext (cubicQuotient_eq_integral hf hf0 hf1 hf2)
  rw [heq]
  exact contDiff_const.mul (Analysis.contDiff_scaled_intervalIntegral hw hf3)

end ContinuousFlexibility.Statements
