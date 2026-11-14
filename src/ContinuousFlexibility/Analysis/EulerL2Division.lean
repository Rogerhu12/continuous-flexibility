module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# An L² estimate for the Euler operator on the unit interval

For `a ≥ 1`, the expression `x u' + a u` controls `u` in L² with
constant two. The proof integrates the derivative of `x u²` and completes
a square. All functions being integrated are continuous on the closed unit
interval, so no improper integral or unproved boundary limit is used.

This is the estimate needed after differentiating a smooth division by `x`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

/-- On the unit interval the L² seminorm of a continuous real function is
the square root of its ordinary square integral. -/
theorem eLpNorm_two_eq_ofReal_sqrt_intervalIntegral {v : ℝ → ℝ}
    (hv : Continuous v) :
    eLpNorm v 2 (volume.restrict (Ioo (0 : ℝ) 1)) =
      ENNReal.ofReal (Real.sqrt (∫ y in (0 : ℝ)..1, v y ^ 2)) := by
  have hmem : MemLp v 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
    apply (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).mpr
    exact (hv.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  rw [← one_div, ← Real.sqrt_eq_rpow]

/-- The square-integral estimate follows from
`4 (x u' + a u)² - u² - 2 (x u²)' = (2 (x u' + a u) - u)² + 4 (a-1) u²`.
The boundary contribution is `u(1)² ≥ 0`. -/
theorem integral_sq_le_four_euler {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    {a : ℝ} (ha : 1 ≤ a) :
    (∫ y in (0 : ℝ)..1, u y ^ 2) ≤
      4 * ∫ y in (0 : ℝ)..1, (y * deriv u y + a * u y) ^ 2 := by
  let H : ℝ → ℝ := fun y => y * deriv u y + a * u y
  let V' : ℝ → ℝ := fun y => u y ^ 2 + 2 * y * u y * deriv u y
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hH : Continuous H :=
    (continuous_id.mul hdu).add (continuous_const.mul hu.continuous)
  have hV' : Continuous V' :=
    (hu.continuous.pow 2).add
      (((continuous_const.mul continuous_id).mul hu.continuous).mul hdu)
  have huInt : IntervalIntegrable (fun y => u y ^ 2) volume 0 1 :=
    (hu.continuous.pow 2).intervalIntegrable 0 1
  have hHInt : IntervalIntegrable (fun y => H y ^ 2) volume 0 1 :=
    (hH.pow 2).intervalIntegrable 0 1
  have hVInt : IntervalIntegrable V' volume 0 1 := hV'.intervalIntegrable 0 1
  have hVderiv (y : ℝ) : HasDerivAt (fun t => t * u t ^ 2) (V' y) y := by
    have hd := (hu.differentiable (by simp) y).hasDerivAt
    convert (hasDerivAt_id y).fun_mul (hd.fun_pow 2) using 1 <;>
      dsimp only [V', id] <;> ring
  have hFTC : (∫ y in (0 : ℝ)..1, V' y) = u 1 ^ 2 := by
    simpa only [one_mul, zero_mul, sub_zero] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => hVderiv y) hVInt)
  have hpoint (y : ℝ) : u y ^ 2 + 2 * V' y ≤ 4 * H y ^ 2 := by
    have hpos : 0 ≤ (2 * H y - u y) ^ 2 + 4 * ((a - 1) * u y ^ 2) :=
      add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
        (mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg _)))
    apply sub_nonneg.mp
    convert hpos using 1 <;> dsimp only [H, V'] <;> ring
  have hmono := intervalIntegral.integral_mono_on zero_le_one
    (huInt.add (hVInt.const_mul 2)) (hHInt.const_mul 4) (fun y _ => hpoint y)
  have hbound : (∫ y in (0 : ℝ)..1, u y ^ 2) + 2 * u 1 ^ 2 ≤
      4 * ∫ y in (0 : ℝ)..1, H y ^ 2 := by
    simpa only [intervalIntegral.integral_add huInt (hVInt.const_mul 2),
      intervalIntegral.integral_const_mul, hFTC] using hmono
  dsimp only [H] at hbound
  linarith only [hbound, sq_nonneg (u 1)]

/-- The Euler expression controls the full L² norm, with no condition on
the values of `u` at either endpoint. -/
theorem eLpNorm_le_two_euler {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    {a : ℝ} (ha : 1 ≤ a) :
    eLpNorm u 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤
      ENNReal.ofReal 2 *
        eLpNorm (fun y => y * deriv u y + a * u y) 2
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hH : Continuous (fun y => y * deriv u y + a * u y) :=
    (continuous_id.mul hdu).add (continuous_const.mul hu.continuous)
  rw [eLpNorm_two_eq_ofReal_sqrt_intervalIntegral hu.continuous,
    eLpNorm_two_eq_ofReal_sqrt_intervalIntegral hH]
  have hroot := Real.sqrt_le_sqrt (integral_sq_le_four_euler hu ha)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hroot
  have hfour : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hfour] at hroot
  exact (ENNReal.ofReal_le_ofReal hroot).trans_eq (ENNReal.ofReal_mul (by norm_num))

end ContinuousFlexibility.Analysis
