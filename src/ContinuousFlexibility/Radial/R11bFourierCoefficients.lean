import ContinuousFlexibility.Radial.EvenFourierBasis
import ContinuousFlexibility.Radial.R11bModeL2
import ContinuousFlexibility.Radial.R11bPhysicalCompleteness
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Square summability of actual even Fourier coefficients

Finite Bessel inequalities are integrated in the radial variable. All
coefficients are the original normalized angular integrals of the field.
The zero coefficient is the mean, and no pointwise Fourier convergence is used.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def evenFourierCoefficient {α : Type*} (f : α × ℝ → ℝ) (n : ℕ) (r : α) : ℝ :=
  angularPairing (fun θ => f (r, θ)) (evenCosineBasis n)

@[simp]
theorem evenFourierCoefficient_zero {α : Type*} (f : α × ℝ → ℝ) (r : α) :
    evenFourierCoefficient f 0 r = angularAverage (fun θ => f (r, θ)) := by
  simp only [evenFourierCoefficient, angularPairing, evenCosineBasis_zero, mul_one]

theorem evenFourierCoefficient_zero_physical (f : PolarPoint → ℝ) (r : ℝ) :
    evenFourierCoefficient f 0 r = radialAngularMean (fun θ => f (r, θ)) := by
  rw [evenFourierCoefficient_zero]
  simp only [angularAverage, radialAngularMean, one_div]

theorem evenFourierCoefficient_eq_referenceMode (f : PolarPoint → ℝ) {n : ℕ} (hn : n ≠ 0) :
    evenFourierCoefficient f n = referenceMode f (2 * n) := by
  funext r
  simp only [evenFourierCoefficient, evenCosineBasis_of_ne_zero hn,
    angularPairing, referenceMode, angularAverage, radialAngularMean, one_div]

theorem evenFourierCoefficient_eq_integral {α : Type*} (f : α × ℝ → ℝ) (n : ℕ) :
    evenFourierCoefficient f n =
      fun r => ∫ θ, f (r, θ) * evenCosineBasis n θ ∂angularMeanMeasure := by
  funext r
  exact angularAverage_eq_integral_angularMeanMeasure _

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem evenFourierCoefficient_memLp {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod angularMeanMeasure)) (n : ℕ) :
    MemLp (evenFourierCoefficient f n) 2 μ := by
  rw [evenFourierCoefficient_eq_integral]
  exact (r11b_memLp_modeCoefficient hf (evenCosineBasis_memLp n)).1

theorem evenFourierCoefficient_finite_energy_le {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod angularMeanMeasure)) (J : Finset ℕ) :
    (∑ n ∈ J, ∫ r, evenFourierCoefficient f n r ^ 2 ∂μ) ≤
      ∫ z, f z ^ 2 ∂μ.prod angularMeanMeasure := by
  have hpoint : ∀ᵐ r ∂μ,
      (∑ n ∈ J, evenFourierCoefficient f n r ^ 2) ≤
        ∫ θ, f (r, θ) ^ 2 ∂angularMeanMeasure := by
    filter_upwards [r11b_memLp_product_sections hf] with r hr
    have h := angularPairing_finite_bessel J evenCosineBasis
      (memLp_angularInterval_of_mean hr)
      (fun n _ => evenCosineBasis_memLp_interval n)
      (fun n _ m _ => angularPairing_evenCosineBasis n m)
    simpa only [evenFourierCoefficient, angularAverage_eq_integral_angularMeanMeasure] using h
  have hi : ∀ n ∈ J, Integrable (fun r => evenFourierCoefficient f n r ^ 2) μ :=
    fun n _ => (evenFourierCoefficient_memLp hf n).integrable_sq
  calc
    (∑ n ∈ J, ∫ r, evenFourierCoefficient f n r ^ 2 ∂μ) =
        ∫ r, ∑ n ∈ J, evenFourierCoefficient f n r ^ 2 ∂μ :=
      (integral_finsetSum J hi).symm
    _ ≤ ∫ r, ∫ θ, f (r, θ) ^ 2 ∂angularMeanMeasure ∂μ :=
      integral_mono_ae (integrable_finsetSum J hi) hf.integrable_sq.integral_prod_left hpoint
    _ = ∫ z, f z ^ 2 ∂μ.prod angularMeanMeasure :=
      (integral_prod _ hf.integrable_sq).symm

theorem evenFourierCoefficient_energy_summable {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod angularMeanMeasure)) :
    Summable (fun n => ∫ r, evenFourierCoefficient f n r ^ 2 ∂μ) :=
  summable_of_sum_le (fun _ => integral_nonneg fun _ => sq_nonneg _)
    (evenFourierCoefficient_finite_energy_le hf)

theorem evenFourierCoefficient_tsum_energy_le {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod angularMeanMeasure)) :
    (∑' n, ∫ r, evenFourierCoefficient f n r ^ 2 ∂μ) ≤
      ∫ z, f z ^ 2 ∂μ.prod angularMeanMeasure :=
  (evenFourierCoefficient_energy_summable hf).tsum_le_of_sum_le
    (evenFourierCoefficient_finite_energy_le hf)

end

end ContinuousFlexibility.Radial
