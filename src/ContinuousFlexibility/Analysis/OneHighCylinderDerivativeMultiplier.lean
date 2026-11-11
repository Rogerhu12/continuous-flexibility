import ContinuousFlexibility.Analysis.OneHighCylinderSobolevWeights

/-!
# The actual physical mixed derivative multiplier

Radial Fourier frequency uses the 2π convention and angular frequency uses
the physical period. This shared definition is independent of frequency
cutoffs and the reverse derivative-membership argument.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

def cylinderDerivativeMultiplier (P : ℝ) (i j : ℕ) (ζ : ℝ × ℤ) : ℂ :=
  (Complex.I * ((2 * Real.pi * ζ.1 : ℝ) : ℂ)) ^ i *
    (Complex.I * (((2 * Real.pi / P) * (ζ.2 : ℝ) : ℝ) : ℂ)) ^ j

@[simp] theorem cylinderDerivativeMultiplier_zero_zero (P : ℝ) (ζ : ℝ × ℤ) :
    cylinderDerivativeMultiplier P 0 0 ζ = 1 := by
  simp only [cylinderDerivativeMultiplier, pow_zero, one_mul]

theorem cylinderDerivativeMultiplier_radial_succ (P : ℝ) (i j : ℕ) (ζ : ℝ × ℤ) :
    cylinderDerivativeMultiplier P (i + 1) j ζ =
      (Complex.I * ((2 * Real.pi * ζ.1 : ℝ) : ℂ)) * cylinderDerivativeMultiplier P i j ζ := by
  simp only [cylinderDerivativeMultiplier, pow_succ]
  ring

theorem cylinderDerivativeMultiplier_angular_succ (P : ℝ) (i j : ℕ) (ζ : ℝ × ℤ) :
    cylinderDerivativeMultiplier P i (j + 1) ζ =
      (Complex.I * (((2 * Real.pi / P) * (ζ.2 : ℝ) : ℝ) : ℂ)) *
        cylinderDerivativeMultiplier P i j ζ := by
  simp only [cylinderDerivativeMultiplier, pow_succ]
  ring

theorem cylinderDerivativeMultiplier_mul (P : ℝ) (i j k l : ℕ) (ζ : ℝ × ℤ) :
    cylinderDerivativeMultiplier P i j ζ * cylinderDerivativeMultiplier P k l ζ =
      cylinderDerivativeMultiplier P (i + k) (j + l) ζ := by
  simp only [cylinderDerivativeMultiplier, pow_add]
  ring

theorem continuous_cylinderDerivativeMultiplier (P : ℝ) (i j : ℕ) :
    Continuous (cylinderDerivativeMultiplier P i j) := by
  unfold cylinderDerivativeMultiplier
  fun_prop

theorem measurable_cylinderDerivativeMultiplier (P : ℝ) (i j : ℕ) :
    Measurable (cylinderDerivativeMultiplier P i j) :=
  (continuous_cylinderDerivativeMultiplier P i j).measurable

theorem norm_cylinderDerivativeMultiplier (P : ℝ) (i j : ℕ) (ζ : ℝ × ℤ) :
    ‖cylinderDerivativeMultiplier P i j ζ‖ =
      |2 * Real.pi * ζ.1| ^ i * |(2 * Real.pi / P) * (ζ.2 : ℝ)| ^ j := by
  simp only [cylinderDerivativeMultiplier, norm_mul, norm_pow, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, one_mul, abs_mul]

theorem norm_cylinderDerivativeMultiplier_le_weight (P : ℝ) (i j s : ℕ)
    (hij : i + j ≤ s) (ζ : ℝ × ℤ) :
    ‖cylinderDerivativeMultiplier P i j ζ‖ ≤
      cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ^ s := by
  rw [norm_cylinderDerivativeMultiplier]
  exact cylinder_mixedFrequency_le_weight (2 * Real.pi) (2 * Real.pi / P) ζ hij

theorem cylinderDerivativeMultiplier_mul_memLp {P : ℝ} {F : ℝ × ℤ → ℂ}
    (hF : Measurable F) {s i j : ℕ} (hij : i + j ≤ s)
    (hFs : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ) F)
        2 cylinderFrequencyMeasure) :
    MemLp (fun ζ => cylinderDerivativeMultiplier P i j ζ * F ζ) 2 cylinderFrequencyMeasure := by
  apply hFs.of_le ((measurable_cylinderDerivativeMultiplier P i j).mul hF).aestronglyMeasurable
  exact Eventually.of_forall fun ζ => by
    simp only [Pi.mul_apply]
    rw [norm_mul, cylinder_norm_frequencyWeighted_nat]
    exact mul_le_mul_of_nonneg_right
      (norm_cylinderDerivativeMultiplier_le_weight P i j s hij ζ) (norm_nonneg _)

end ContinuousFlexibility.Analysis
