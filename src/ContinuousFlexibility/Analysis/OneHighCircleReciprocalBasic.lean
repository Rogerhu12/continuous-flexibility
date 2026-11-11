import ContinuousFlexibility.Analysis.OneHighCircleInverseGeometry
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Algebra.Ring.Periodic

/-!
# Actual derivatives of the reciprocal derivative defect

On its natural domain this function is -z / (1 + z). The chosen total real
representative makes its value at zero and every positive-order derivative
transparent; the arbitrary value at the excluded pole plays no role.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function Set
open scoped ContDiff

def circleReciprocalDefect (z : ℝ) : ℝ := (1 + z)⁻¹ - 1

@[simp] theorem circleReciprocalDefect_zero : circleReciprocalDefect 0 = 0 := by
  simp only [circleReciprocalDefect, add_zero, inv_one, sub_self]

theorem circleReciprocalDefect_eq_neg_div {z : ℝ} (hz : 1 + z ≠ 0) :
    circleReciprocalDefect z = -z / (1 + z) := by
  rw [circleReciprocalDefect]
  field_simp [hz] <;> ring

theorem contDiffAt_circleReciprocalDefect (z : ℝ) (hz : 1 + z ≠ 0) :
    ContDiffAt ℝ ∞ circleReciprocalDefect z :=
  ((contDiffAt_const.add contDiffAt_id).inv hz).sub contDiffAt_const

theorem circleReciprocalDefect_iteratedDeriv {n : ℕ} (hn : 0 < n) (z : ℝ) :
    iteratedDeriv n circleReciprocalDefect z =
      (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * ((1 + z) ^ (n + 1))⁻¹ := by
  have he : circleReciprocalDefect = fun y : ℝ => -1 + 1 / (1 + y) := by
    funext y
    simp only [circleReciprocalDefect, one_div]
    ring
  have hshift := congrFun (iteratedDeriv_comp_const_add n (fun y : ℝ => 1 / y) 1) z
  have hp := iteratedDerivWithin_one_div (𝕜 := ℝ) n isOpen_univ (mem_univ (1 + z))
  have hexp : (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) := by omega
  calc
    _ = iteratedDeriv n (fun y : ℝ => 1 / (1 + y)) z := by
      rw [he, iteratedDeriv_const_add hn (-1)]
    _ = iteratedDeriv n (fun y : ℝ => 1 / y) (1 + z) := hshift
    _ = _ := by
      simpa only [iteratedDerivWithin_univ, hexp, zpow_neg, zpow_natCast] using hp

/-- Bounds on every positive derivative, determined by a lower bound for
the denominator. -/
def circleReciprocalDerivativeBound (c : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * ((min 1 c) ^ (n + 1))⁻¹

theorem circleReciprocalDerivativeBound_nonneg {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 ≤ circleReciprocalDerivativeBound c n := by
  have hd : 0 < min (1 : ℝ) c := lt_min (by norm_num) hc
  exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (pow_nonneg hd.le _))

theorem circleReciprocalDefect_iteratedDeriv_bound {c : ℝ} (hc : 0 < c)
    {z : ℝ} (hz : min 1 c - 1 ≤ z) {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedDeriv n circleReciprocalDefect z‖ ≤ circleReciprocalDerivativeBound c n := by
  have hd : 0 < min (1 : ℝ) c := lt_min (by norm_num) hc
  have hden : min 1 c ≤ 1 + z := by linarith
  have hdenpos : 0 < 1 + z := hd.trans_le hden
  have hpow : (min 1 c) ^ (n + 1) ≤ (1 + z) ^ (n + 1) :=
    pow_le_pow_left₀ hd.le hden (n + 1)
  have hinv : ((1 + z) ^ (n + 1))⁻¹ ≤ ((min 1 c) ^ (n + 1))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hd _) hpow
  rw [circleReciprocalDefect_iteratedDeriv (by omega) z,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hdenpos.le _))]
  exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)

theorem periodic_circleReciprocal_comp {P : ℝ} {v : ℝ → ℝ} (hp : Periodic v P) :
    Periodic (circleReciprocalDefect ∘ v) P := by
  intro x
  dsimp only [Function.comp_def]
  rw [hp x]

theorem contDiff_circleReciprocal_comp {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c - 1 ≤ v x) :
    ContDiff ℝ ∞ (circleReciprocalDefect ∘ v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hden : 0 < 1 + v x := by linarith [hlower x]
  exact (contDiffAt_circleReciprocalDefect (v x) hden.ne').comp x hv.contDiffAt

/-- The actual derivative defect of the inverse is the reciprocal function
of the actual forward derivative defect, evaluated at the inverse point. -/
theorem circleInverse_deriv_sub_one_eq_reciprocal {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
    (hι : ∀ x, h (ι x) = x) (x : ℝ) (hne : deriv h (ι x) ≠ 0) :
    deriv ι x - 1 = circleReciprocalDefect (deriv h (ι x) - 1) := by
  rw [circleInverse_deriv hh hi hι x hne, circleReciprocalDefect]
  congr 2
  ring

end ContinuousFlexibility.Analysis
