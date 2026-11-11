import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The missing base-point control in the composition estimate

The manuscript's Lemma 7.2(iii) permits a constant to depend only on the
Fourier norm of the input and on derivatives of the outer function over
the input's range. On the circle, take the fixed input `v = 1`. The
polynomials `M * (2*x - x^2)` all vanish at zero and have derivative zero
on the range `{1}`, but their values at one are arbitrarily large.

The explicit interval integrals below are the ordinary `L²` norms of
these constant functions on a circle of any positive period. No new
Sobolev norm is introduced. At order zero a linear family separately
shows that first-derivative control cannot be omitted.

The corrected composition estimate must control the first derivative
along the segments from zero to the input range, also at order zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Real MeasureTheory
open scoped ContDiff

/-- A polynomial whose derivative vanishes at the constant input one. -/
def oneHighFactorQuadratic (M : ℝ) (x : ℝ) : ℝ := M * (2 * x - x ^ 2)

theorem contDiff_oneHighFactorQuadratic (M : ℝ) :
    ContDiff ℝ ∞ (oneHighFactorQuadratic M) :=
  contDiff_const.mul ((contDiff_const.mul contDiff_id).sub (contDiff_id.pow 2))

@[simp] theorem oneHighFactorQuadratic_zero (M : ℝ) :
    oneHighFactorQuadratic M 0 = 0 := by
  simp [oneHighFactorQuadratic]

@[simp] theorem oneHighFactorQuadratic_one (M : ℝ) :
    oneHighFactorQuadratic M 1 = M := by
  norm_num [oneHighFactorQuadratic]

theorem hasDerivAt_oneHighFactorQuadratic (M x : ℝ) :
    HasDerivAt (oneHighFactorQuadratic M) (M * (2 - 2 * x)) x := by
  have h := (((hasDerivAt_id x).const_mul (2 : ℝ)).fun_sub
    ((hasDerivAt_id x).fun_pow 2)).const_mul M
  simpa [oneHighFactorQuadratic] using h

@[simp] theorem deriv_oneHighFactorQuadratic_one (M : ℝ) :
    deriv (oneHighFactorQuadratic M) 1 = 0 := by
  simpa using (hasDerivAt_oneHighFactorQuadratic M 1).deriv

/-- Even requiring the outer function to vanish at zero does not repair
the claimed dependence on its derivative over the singleton range `{1}`. -/
theorem oneHighFactor_no_range_only_composition_bound :
    ¬ ∃ C : ℝ, ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → Φ 0 = 0 → deriv Φ 1 = 0 →
      |Φ 1 - Φ 0| ≤ C := by
  rintro ⟨C, hC⟩
  have h := hC (oneHighFactorQuadratic (C + 1))
    (contDiff_oneHighFactorQuadratic (C + 1)) (oneHighFactorQuadratic_zero (C + 1))
    (deriv_oneHighFactorQuadratic_one (C + 1))
  simp only [oneHighFactorQuadratic_one, oneHighFactorQuadratic_zero, sub_zero] at h
  linarith only [h, le_abs_self (C + 1)]

/-- The ordinary square-integral expression for a constant function. -/
theorem oneHighFactor_constant_interval_l2 (P c : ℝ) :
    sqrt (∫ θ in (0 : ℝ)..P, c ^ 2) = |c| * sqrt P := by
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  rw [sqrt_mul' P (sq_nonneg c), sqrt_sq_eq_abs, mul_comm]

/-- For every positive circle period the same polynomial family
disproves a uniform bound on the actual `L²` norms of constant outputs.
The right side is the `L²` norm of the fixed constant input one. -/
theorem oneHighFactor_no_range_only_circle_constant_l2_bound {P : ℝ} (hP : 0 < P) :
    ¬ ∃ C : ℝ, ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → Φ 0 = 0 → deriv Φ 1 = 0 →
      sqrt (∫ θ in (0 : ℝ)..P, (Φ 1 - Φ 0) ^ 2) ≤
        C * sqrt (∫ θ in (0 : ℝ)..P, (1 : ℝ) ^ 2) := by
  rintro ⟨C, hC⟩
  have h := hC (oneHighFactorQuadratic (C + 1))
    (contDiff_oneHighFactorQuadratic (C + 1)) (oneHighFactorQuadratic_zero (C + 1))
    (deriv_oneHighFactorQuadratic_one (C + 1))
  simp only [oneHighFactorQuadratic_one, oneHighFactorQuadratic_zero, sub_zero] at h
  rw [oneHighFactor_constant_interval_l2, oneHighFactor_constant_interval_l2] at h
  simp only [abs_one, one_mul] at h
  have hbound : |C + 1| ≤ C := (mul_le_mul_iff_left₀ (sqrt_pos.mpr hP)).mp h
  linarith only [hbound, le_abs_self (C + 1)]

/-- A linear family isolates the missing derivative control at order zero. -/
def oneHighFactorLinear (M : ℝ) (x : ℝ) : ℝ := M * x

theorem contDiff_oneHighFactorLinear (M : ℝ) :
    ContDiff ℝ ∞ (oneHighFactorLinear M) :=
  contDiff_const.mul contDiff_id

@[simp] theorem oneHighFactorLinear_zero (M : ℝ) : oneHighFactorLinear M 0 = 0 := by
  simp [oneHighFactorLinear]

@[simp] theorem oneHighFactorLinear_one (M : ℝ) : oneHighFactorLinear M 1 = M := by
  simp [oneHighFactorLinear]

/-- At Sobolev order zero the empty list of derivative bounds cannot
provide a uniform composition constant, even for linear outer functions. -/
theorem oneHighFactor_no_derivative_free_composition_bound :
    ¬ ∃ C : ℝ, ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → Φ 0 = 0 → |Φ 1 - Φ 0| ≤ C := by
  rintro ⟨C, hC⟩
  have h := hC (oneHighFactorLinear (C + 1))
    (contDiff_oneHighFactorLinear (C + 1)) (oneHighFactorLinear_zero (C + 1))
  simp only [oneHighFactorLinear_one, oneHighFactorLinear_zero, sub_zero] at h
  linarith only [h, le_abs_self (C + 1)]

/-- The order-zero obstruction also holds for the ordinary circle
`L²` expression at every positive period. -/
theorem oneHighFactor_no_derivative_free_circle_l2_bound {P : ℝ} (hP : 0 < P) :
    ¬ ∃ C : ℝ, ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → Φ 0 = 0 →
      sqrt (∫ θ in (0 : ℝ)..P, (Φ 1 - Φ 0) ^ 2) ≤
        C * sqrt (∫ θ in (0 : ℝ)..P, (1 : ℝ) ^ 2) := by
  rintro ⟨C, hC⟩
  have h := hC (oneHighFactorLinear (C + 1))
    (contDiff_oneHighFactorLinear (C + 1)) (oneHighFactorLinear_zero (C + 1))
  simp only [oneHighFactorLinear_one, oneHighFactorLinear_zero, sub_zero] at h
  rw [oneHighFactor_constant_interval_l2, oneHighFactor_constant_interval_l2] at h
  simp only [abs_one, one_mul] at h
  have hbound : |C + 1| ≤ C := (mul_le_mul_iff_left₀ (sqrt_pos.mpr hP)).mp h
  linarith only [hbound, le_abs_self (C + 1)]

end ContinuousFlexibility.Analysis
