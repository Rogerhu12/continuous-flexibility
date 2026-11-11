import ContinuousFlexibility.Radial.FiniteFourierBessel
import ContinuousFlexibility.Radial.AngularMeanProbability

/-!
# The real even half-turn Fourier basis including the mean

The zero basis vector is the constant one. Positive indices use the normalized
mode sqrt(2) * cos(2*n*theta), so every basis vector has unit angular mean square.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open scoped BigOperators

/-- The mean is indexed by zero; it is not the mode sqrt(2) * cos(0). -/
def evenCosineBasis (n : ℕ) (θ : ℝ) : ℝ :=
  if n = 0 then 1 else cosineMode (2 * n) θ

@[simp]
theorem evenCosineBasis_zero : evenCosineBasis 0 = (fun _ : ℝ => 1) := by
  funext θ
  simp only [evenCosineBasis, if_pos rfl]

theorem evenCosineBasis_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    evenCosineBasis n = cosineMode (2 * n) := by
  funext θ
  simp only [evenCosineBasis, if_neg hn]

theorem continuous_evenCosineBasis (n : ℕ) : Continuous (evenCosineBasis n) := by
  by_cases hn : n = 0
  · subst n
    rw [evenCosineBasis_zero]
    exact continuous_const
  · rw [evenCosineBasis_of_ne_zero hn]
    exact continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))

theorem evenCosineBasis_memLp_interval (n : ℕ) :
    MemLp (evenCosineBasis n) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
  angularInterval_memLp_of_continuous (continuous_evenCosineBasis n)

theorem evenCosineBasis_memLp (n : ℕ) :
    MemLp (evenCosineBasis n) 2 angularMeanMeasure :=
  memLp_angularMeanMeasure (evenCosineBasis_memLp_interval n)

theorem evenCosineBasis_periodic (n : ℕ) :
    Function.Periodic (evenCosineBasis n) Real.pi := by
  by_cases hn : n = 0
  · subst n
    rw [evenCosineBasis_zero]
    exact fun _ => rfl
  · rw [evenCosineBasis_of_ne_zero hn]
    exact cosineMode_even_frequency_periodic n

theorem evenCosineBasis_even (n : ℕ) : Function.Even (evenCosineBasis n) := by
  by_cases hn : n = 0
  · subst n
    rw [evenCosineBasis_zero]
    exact fun _ => rfl
  · rw [evenCosineBasis_of_ne_zero hn]
    exact cosineMode_even (2 * n)

theorem angularAverage_evenCosineBasis (n : ℕ) :
    angularAverage (evenCosineBasis n) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    rw [evenCosineBasis_zero, angularAverage_eq_integral_angularMeanMeasure]
    simp
  · rw [evenCosineBasis_of_ne_zero hn, if_neg hn]
    exact angularAverage_cosineMode (2 * n) (by omega)

theorem angularPairing_evenCosineBasis (n m : ℕ) :
    angularPairing (evenCosineBasis n) (evenCosineBasis m) =
      if n = m then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simpa only [evenCosineBasis_zero, angularPairing, one_mul, eq_comm] using
      angularAverage_evenCosineBasis m
  · by_cases hm : m = 0
    · subst m
      simpa only [evenCosineBasis_zero, angularPairing, mul_one] using
        angularAverage_evenCosineBasis n
    · rw [evenCosineBasis_of_ne_zero hn, evenCosineBasis_of_ne_zero hm]
      have heq : 2 * n = 2 * m ↔ n = m := by omega
      simpa only [heq] using
        angularPairing_cosineMode (2 * n) (2 * m) (by omega) (by omega)

theorem integral_sq_evenCosineBasis (n : ℕ) :
    (∫ θ, evenCosineBasis n θ ^ 2 ∂angularMeanMeasure) = 1 := by
  rw [← angularAverage_eq_integral_angularMeanMeasure]
  simpa only [angularPairing, pow_two, if_pos rfl] using angularPairing_evenCosineBasis n n

theorem integral_mul_evenCosineBasis_of_ne {n m : ℕ} (hnm : n ≠ m) :
    (∫ θ, evenCosineBasis n θ * evenCosineBasis m θ ∂angularMeanMeasure) = 0 := by
  rw [← angularAverage_eq_integral_angularMeanMeasure]
  change angularPairing (evenCosineBasis n) (evenCosineBasis m) = 0
  rw [angularPairing_evenCosineBasis, if_neg hnm]

theorem memLp_angularInterval_of_mean {f : ℝ → ℝ}
    (hf : MemLp f 2 angularMeanMeasure) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have h := hf.smul_measure (c := ENNReal.ofReal (2 * Real.pi)) ENNReal.ofReal_ne_top
  have hcancel : (2 * Real.pi) * (1 / (2 * Real.pi)) = 1 := by
    rw [mul_comm]
    exact div_mul_cancel₀ 1 (by positivity)
  have hmeasure : ENNReal.ofReal (2 * Real.pi) • angularMeanMeasure =
      volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [angularMeanMeasure, smul_smul, ← ENNReal.ofReal_mul (by positivity), hcancel,
      ENNReal.ofReal_one, one_smul]
  rwa [hmeasure] at h

end

end ContinuousFlexibility.Radial
