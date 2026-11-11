import ContinuousFlexibility.Analysis.CubicDivisionSmooth
import ContinuousFlexibility.Analysis.EulerL2Division
import ContinuousFlexibility.Analysis.IteratedDerivLinearFactor

/-!
# Cubic division with three derivatives lost

The Euler estimate controls each smooth division by the coordinate with
constant two. Applying it to the three global smooth factors of a function
with a cubic zero gives a uniform constant eight, at every derivative order.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace ContinuousFlexibility.Analysis

/-- A smooth linear factor costs one derivative and a factor of two in L².
The estimate is uniform in the derivative order. -/
theorem eLpNorm_iteratedDeriv_le_two_linearFactor {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (s : ℕ) :
    eLpNorm (iteratedDeriv s u) 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤
      ENNReal.ofReal 2 * eLpNorm (iteratedDeriv (s + 1) (fun y => y * u y)) 2
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hus : ContDiff ℝ ∞ (iteratedDeriv s u) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv s hu
  have ha : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have h := eLpNorm_le_two_euler hus ha
  have heq : (fun y => y * deriv (iteratedDeriv s u) y +
      ((s + 1 : ℕ) : ℝ) * iteratedDeriv s u y) =
      iteratedDeriv (s + 1) (fun y => y * u y) := by
    funext y
    simpa only [iteratedDeriv_succ] using
      (iteratedDeriv_succ_linearFactor hu s y).symm
  rw [heq] at h
  exact h

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

/-- Cubic division is bounded in every derivative order by the derivative
three orders higher of the original function. The constant is always eight. -/
theorem eLpNorm_iteratedDeriv_cubicQuotient {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0)
    (hf2 : iteratedDeriv 2 f 0 = 0) (s : ℕ) :
    eLpNorm (iteratedDeriv s (cubicQuotient f)) 2
        (volume.restrict (Ioo (0 : ℝ) 1)) ≤
      ENNReal.ofReal 8 * eLpNorm (iteratedDeriv (s + 3) f) 2
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
  let q : ℝ → ℝ := cubicQuotient f
  let q₁ : ℝ → ℝ := fun y => y * q y
  let q₂ : ℝ → ℝ := fun y => y * q₁ y
  have hq : ContDiff ℝ ∞ q := contDiff_cubicQuotient hf hf0 hf1 hf2
  have hq₁ : ContDiff ℝ ∞ q₁ := contDiff_id.mul hq
  have hq₂ : ContDiff ℝ ∞ q₂ := contDiff_id.mul hq₁
  have h₀ := Analysis.eLpNorm_iteratedDeriv_le_two_linearFactor hq s
  have h₁ := Analysis.eLpNorm_iteratedDeriv_le_two_linearFactor hq₁ (s + 1)
  have h₂ := Analysis.eLpNorm_iteratedDeriv_le_two_linearFactor hq₂ (s + 2)
  have hfactor : (fun y => y * q₂ y) = f := by
    funext y
    calc
      y * q₂ y = y ^ 3 * cubicQuotient f y := by dsimp only [q₂, q₁, q]; ring
      _ = f y := cube_mul_cubicQuotient hf0 y
  have htwo : (ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal 2) *
      ENNReal.ofReal 2 = ENNReal.ofReal 8 := by norm_num
  calc
    _ ≤ ENNReal.ofReal 2 * eLpNorm (iteratedDeriv (s + 1) q₁) 2
        (volume.restrict (Ioo (0 : ℝ) 1)) := h₀
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal 2 *
        eLpNorm (iteratedDeriv (s + 2) q₂) 2
          (volume.restrict (Ioo (0 : ℝ) 1))) := by
      exact mul_le_mul_right (by simpa only [Nat.add_assoc] using h₁) _
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal 2 * (ENNReal.ofReal 2 *
        eLpNorm (iteratedDeriv (s + 3) f) 2
          (volume.restrict (Ioo (0 : ℝ) 1)))) := by
      apply mul_le_mul_right
      apply mul_le_mul_right
      simpa only [hfactor, Nat.add_assoc] using h₂
    _ = _ := by rw [← mul_assoc, ← mul_assoc, htwo]

end ContinuousFlexibility.Statements
