module

public import ContinuousFlexibility.Analysis.OneHighCircleFourierProduct

/-!
# Absolutely summable character series

An arbitrary absolutely summable coefficient sequence defines a continuous
circle function. Its actual Fourier coefficients are exactly the original
sequence. This is used when constructing functions from mixed cylinder
frequency data, before any physical square-integrability is known.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory

variable {P : ℝ} [Fact (0 < P)]

def circleFourierSeries (a : ℤ → ℂ) : C(AddCircle P, ℂ) :=
  ∑' n : ℤ, a n • (fourier n : C(AddCircle P, ℂ))

theorem summable_circleFourierSeries {a : ℤ → ℂ}
    (ha : Summable (fun n => ‖a n‖)) :
    Summable (fun n : ℤ => a n • (fourier n : C(AddCircle P, ℂ))) := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using ha

theorem circleFourierSeries_hasSum_apply {a : ℤ → ℂ}
    (ha : Summable (fun n => ‖a n‖)) (θ : AddCircle P) :
    HasSum (fun n : ℤ => a n * fourier n θ) (circleFourierSeries (P := P) a θ) := by
  have h := (ContinuousMap.evalCLM (R := ℂ) θ).hasSum
    (summable_circleFourierSeries (P := P) ha).hasSum
  simpa only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul,
    circleFourierSeries] using h

/-- Every coefficient of the actual continuous character series is the
prescribed coefficient, with no finite-support restriction. -/
theorem circle_fourierCoeff_series {a : ℤ → ℂ}
    (ha : Summable (fun n => ‖a n‖)) (m : ℤ) :
    fourierCoeff (circleFourierSeries (P := P) a) m = a m := by
  classical
  have h := (circleFourierCoeffCLM (P := P) m).hasSum
    (summable_circleFourierSeries (P := P) ha).hasSum
  have ht : (fun n : ℤ => circleFourierCoeffCLM m
      (a n • (fourier n : C(AddCircle P, ℂ)))) =
      fun n : ℤ => if n = m then a m else 0 := by
    funext n
    rw [map_smul, circleFourierCoeffCLM_apply, fourierCoeff_fourier]
    by_cases hn : n = m
    · subst n
      simp
    · simp [Pi.single_apply, hn, Ne.symm hn, smul_eq_mul]
  rw [ht] at h
  exact h.unique (hasSum_ite_eq m (a m))

end ContinuousFlexibility.Analysis
