module

public import ContinuousFlexibility.Analysis.OneHighCircleFourierProducts
public import ContinuousFlexibility.Analysis.OneHighCircleSobolevJets

/-!
# The circle one-high-factor estimate for distributed derivatives

The factors are actual successive derivatives of smooth circle functions.
Every integrability premise required by the infinite convolution argument is
derived from that derivative family. The estimate applies to any positive
number of factors and includes total order zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)]

/-- The full circle estimate for an arbitrary distribution of at most `s`
derivatives among any positive number of factors. In normalized Haar measure
the frequency proof gives constant one. -/
theorem circle_derivative_product_oneHigh (k s : ℕ)
    (f : Fin (k + 1) → ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ i, ∀ j : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f i j (y : AddCircle P))
        (f i (j + 1) (x : AddCircle P)) x)
    (a : Fin (k + 1) → ℕ) (ha : ∑ i, a i ≤ s) :
    (eLpNorm (∏ i, f i (a i)) 2 AddCircle.haarAddCircle).toReal ≤
      ∑ j, frequencySobolevNorm Measure.count (circleFrequencyWeight P) (s : ℝ)
          (fourierCoeff (f j 0)) *
        ∏ i ∈ Finset.univ.erase j, frequencyL1Norm Measure.count (fourierCoeff (f i 0)) := by
  have h := circle_eLpNorm_fourierCoeff_prod_le_oneHigh k s
    (fun i => f i (a i))
    (fun i => circle_fourier_memLp_one_of_derivatives (f i) (hderiv i) (a i))
    (fun n => ENNReal.ofReal (circleFrequencyWeight P n))
    (fun n => by simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (circleFrequencyWeight_one_le P n))
    (fun i n => ‖fourierCoeff (f i 0) n‖ₑ) a ha
    (fun i n => circle_enorm_fourierCoeff_derivative_le_weight
      (f i) (hderiv i) (le_refl (a i)) n)
  simp_rw [circle_eLpNorm_weighted_enorm] at h
  have hnorm (i : Fin (k + 1)) :
      eLpNorm (fun n => ‖fourierCoeff (f i 0) n‖ₑ) 1 Measure.count =
        eLpNorm (fourierCoeff (f i 0)) 1 Measure.count :=
    eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable
  simp_rw [hnorm] at h
  have hhigh (i : Fin (k + 1)) :
      MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
        (fourierCoeff (f i 0))) 2 Measure.count :=
    circle_frequencyWeighted_memLp_of_derivatives (f i) (hderiv i) s
  have hlow (i : Fin (k + 1)) : MemLp (fourierCoeff (f i 0)) 1 Measure.count :=
    circle_fourier_memLp_one_of_derivatives (f i) (hderiv i) 0
  have hterm (j : Fin (k + 1)) :
      eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
          (fourierCoeff (f j 0))) 2 Measure.count *
        (∏ i ∈ Finset.univ.erase j, eLpNorm (fourierCoeff (f i 0)) 1 Measure.count) ≠ ∞ :=
    ENNReal.mul_ne_top (hhigh j).ne (ENNReal.prod_ne_top (fun i _ => (hlow i).ne))
  have hr := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun j _ => hterm j)) h
  rw [ENNReal.toReal_sum (fun j _ => hterm j)] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_prod] at hr
  have hprod : (∏ i : Fin (k + 1), (f i (a i) : AddCircle P → ℂ)) =
      ((∏ i : Fin (k + 1), f i (a i) : C(AddCircle P, ℂ)) : AddCircle P → ℂ) := by
    funext θ
    simp only [Finset.prod_apply, ContinuousMap.prod_apply]
  rw [hprod, circle_fourier_l2_toReal] at hr
  simpa only [frequencySobolevNorm, frequencyL1Norm, hprod] using hr

end ContinuousFlexibility.Analysis
