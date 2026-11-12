import ContinuousFlexibility.Analysis.SpacesCircleSpectral
import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Actual diagonal operators on the control Hilbert space

Uniformly bounded scalar coefficients act coordinate by coordinate on
the actual `ControlBanach` space.  A lower absolute bound of `1/2`
constructs the reciprocal multiplier, with both inverse identities and
operator norms at most two.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

/-- The real coefficient multiplier on the actual control sequence space. -/
def n08ControlDiagonal (a : ℕ → ℝ) (ha : ∀ m, |a m| ≤ 2) :
    ControlBanach →L[ℝ] ControlBanach :=
  lpSpectralDiagonal (fun m => ContinuousLinearMap.mul ℝ ℝ (a m))
    (C := 2) (by norm_num) (fun m x => by
      simp only [ContinuousLinearMap.mul_apply', Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (ha m) (abs_nonneg x))

theorem n08ControlDiagonal_apply (a : ℕ → ℝ) (ha : ∀ m, |a m| ≤ 2)
    (u : ControlBanach) (m : ℕ) :
    n08ControlDiagonal a ha u m = a m * u m := by
  rw [n08ControlDiagonal, lpSpectralDiagonal_apply, ContinuousLinearMap.mul_apply']

theorem n08ControlDiagonal_norm_apply_le (a : ℕ → ℝ) (ha : ∀ m, |a m| ≤ 2)
    (u : ControlBanach) :
    ‖n08ControlDiagonal a ha u‖ ≤ 2 * ‖u‖ := by
  unfold n08ControlDiagonal
  exact lpSpectralDiagonal_norm_le _ _ _ u

theorem n08ControlDiagonal_norm_le (a : ℕ → ℝ) (ha : ∀ m, |a m| ≤ 2) :
    ‖n08ControlDiagonal a ha‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (n08ControlDiagonal_norm_apply_le a ha)

theorem n08ControlDiagonal_coefficient_ne_zero (a : ℕ → ℝ)
    (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (m : ℕ) : a m ≠ 0 :=
  abs_pos.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (ha m))

theorem n08ControlDiagonal_reciprocal_bound (a : ℕ → ℝ)
    (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (m : ℕ) : |(a m)⁻¹| ≤ 2 := by
  calc
    |(a m)⁻¹| = 1 / |a m| := by rw [abs_inv, one_div]
    _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) (ha m)
    _ = 2 := by norm_num

/-- The inverse uses the actual reciprocal coefficient on every coordinate. -/
def n08ControlDiagonalInverse (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) :
    ControlBanach →L[ℝ] ControlBanach :=
  n08ControlDiagonal (fun m => (a m)⁻¹) (n08ControlDiagonal_reciprocal_bound a ha)

theorem n08ControlDiagonalInverse_apply (a : ℕ → ℝ)
    (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (u : ControlBanach) (m : ℕ) :
    n08ControlDiagonalInverse a ha u m = (a m)⁻¹ * u m :=
  n08ControlDiagonal_apply _ _ u m

theorem n08ControlDiagonalInverse_norm_le (a : ℕ → ℝ)
    (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) :
    ‖n08ControlDiagonalInverse a ha‖ ≤ 2 :=
  n08ControlDiagonal_norm_le _ _

theorem n08ControlDiagonalInverse_left (a : ℕ → ℝ)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (hhi : ∀ m, |a m| ≤ 2)
    (u : ControlBanach) :
    n08ControlDiagonalInverse a hlo (n08ControlDiagonal a hhi u) = u := by
  apply lp.ext
  funext m
  rw [n08ControlDiagonalInverse_apply, n08ControlDiagonal_apply, ← mul_assoc,
    inv_mul_cancel₀ (n08ControlDiagonal_coefficient_ne_zero a hlo m), one_mul]

theorem n08ControlDiagonalInverse_right (a : ℕ → ℝ)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (hhi : ∀ m, |a m| ≤ 2)
    (u : ControlBanach) :
    n08ControlDiagonal a hhi (n08ControlDiagonalInverse a hlo u) = u := by
  apply lp.ext
  funext m
  rw [n08ControlDiagonal_apply, n08ControlDiagonalInverse_apply, ← mul_assoc,
    mul_inv_cancel₀ (n08ControlDiagonal_coefficient_ne_zero a hlo m), one_mul]

/-- The two bounded control operators are produced from the scalar interval
bound, rather than assumed as part of that bound. -/
theorem exists_n08ControlDiagonal (a : ℕ → ℝ)
    (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m| ∧ |a m| ≤ 2) :
    ∃ J JInverse : ControlBanach →L[ℝ] ControlBanach,
      (∀ u m, J u m = a m * u m) ∧
      (∀ u m, JInverse u m = (a m)⁻¹ * u m) ∧
      (∀ u, JInverse (J u) = u ∧ J (JInverse u) = u) ∧
      ‖J‖ ≤ 2 ∧ ‖JInverse‖ ≤ 2 := by
  let hlo := fun m => (ha m).1
  let hhi := fun m => (ha m).2
  exact ⟨n08ControlDiagonal a hhi, n08ControlDiagonalInverse a hlo,
    n08ControlDiagonal_apply a hhi, n08ControlDiagonalInverse_apply a hlo,
    fun u => ⟨n08ControlDiagonalInverse_left a hlo hhi u,
      n08ControlDiagonalInverse_right a hlo hhi u⟩,
    n08ControlDiagonal_norm_le a hhi, n08ControlDiagonalInverse_norm_le a hlo⟩

end ContinuousFlexibility.Analysis
