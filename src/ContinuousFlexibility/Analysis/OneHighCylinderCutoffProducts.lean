import ContinuousFlexibility.Analysis.OneHighCylinderInverseProducts
import ContinuousFlexibility.Analysis.OneHighCylinderFourierCutoffJets

/-!
# Uniform one-high bounds for genuine cutoff derivative products

Every cutoff derivative is the actual inverse of its multiplied frequency
cutoff. The positive convolution estimate bounds their physical product
uniformly by the original uncut Fourier-L1 and Sobolev norms.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)]

theorem cylinder_eLpNorm_weighted_enorm (s : ℕ) (F : ℝ × ℤ → ℂ)
    (hF : AEStronglyMeasurable F cylinderFrequencyMeasure) (p : ℝ≥0∞) :
    eLpNorm (fun ζ => ENNReal.ofReal
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ) ^ s * ‖F ζ‖ₑ)
        p cylinderFrequencyMeasure =
      eLpNorm (frequencyWeighted
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ) F)
          p cylinderFrequencyMeasure := by
  have he : (fun ζ => ENNReal.ofReal
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ) ^ s * ‖F ζ‖ₑ) =
      fun ζ => ‖frequencyWeighted
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ) F ζ‖ₑ := by
    funext ζ
    rw [frequencyWeighted_enorm (cylinderFrequencyWeight_pos _ _ ζ), ENNReal.rpow_natCast]
  rw [he]
  exact eLpNorm_enorm _ (frequencyWeighted_aestronglyMeasurable
    (continuous_cylinderFrequencyWeight _ _).measurable.aemeasurable hF _)

theorem norm_cylinderFrequencyCutoffJet_le_weight
    (N i j : ℕ) (F : ℝ × ℤ → ℂ) (ζ : ℝ × ℤ) :
    ‖cylinderFrequencyCutoffJet (P := P) N F i j ζ‖ ≤
      cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ^ (i + j) * ‖F ζ‖ := by
  by_cases h : cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ)
  · rw [cylinderFrequencyCutoffJet, cylinderFrequencyCutoff, if_pos h, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_cylinderDerivativeMultiplier_le_weight P i j (i + j) le_rfl ζ) (norm_nonneg _)
  · rw [cylinderFrequencyCutoffJet, cylinderFrequencyCutoff, if_neg h, mul_zero, norm_zero]
    positivity

theorem enorm_cylinderFrequencyCutoffJet_le_weight
    (N i j : ℕ) (F : ℝ × ℤ → ℂ) (ζ : ℝ × ℤ) :
    ‖cylinderFrequencyCutoffJet (P := P) N F i j ζ‖ₑ ≤
      ENNReal.ofReal (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ) ^ (i + j) *
        ‖F ζ‖ₑ := by
  have h := ENNReal.ofReal_le_ofReal
    (norm_cylinderFrequencyCutoffJet_le_weight (P := P) N i j F ζ)
  simpa only [ENNReal.ofReal_mul
      (pow_nonneg (cylinderFrequencyWeight_pos _ _ ζ).le (i + j)),
    ENNReal.ofReal_pow (cylinderFrequencyWeight_pos _ _ ζ).le, ofReal_norm] using h

/-- This uniform estimate retains the exact original endpoint norms; it
does not require higher derivative integrability of the original data. -/
theorem cylinder_cutoff_derivative_product_oneHigh (k s N : ℕ)
    {F : Fin (k + 1) → (ℝ × ℤ) → ℂ}
    (hF : ∀ i, Measurable (F i))
    (hF1 : ∀ i, MemLp (F i) 1 cylinderFrequencyMeasure)
    (hF2 : ∀ i, MemLp (F i) 2 cylinderFrequencyMeasure)
    (a b : Fin (k + 1) → ℕ) (hab : ∑ i, (a i + b i) ≤ s) :
    MemLp (fun p : ℝ × AddCircle P => ∏ i,
      (cylinderCutoffJet (F i) (hF i) (memLp_one_iff_integrable.mp (hF1 i)) N).jet
        (a i) (b i) p) 2 (cylinderPhysicalMeasure P) ∧
    eLpNorm (fun p : ℝ × AddCircle P => ∏ i,
      (cylinderCutoffJet (F i) (hF i) (memLp_one_iff_integrable.mp (hF1 i)) N).jet
        (a i) (b i) p) 2 (cylinderPhysicalMeasure P) ≤
      ∑ j, eLpNorm (frequencyWeighted
          (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ) (F j))
          2 cylinderFrequencyMeasure *
        ∏ i ∈ Finset.univ.erase j, eLpNorm (F i) 1 cylinderFrequencyMeasure := by
  have hw : Measurable (fun ζ : ℝ × ℤ =>
      ENNReal.ofReal (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ)) :=
    (continuous_cylinderFrequencyWeight _ _).measurable.ennreal_ofReal
  have hw1 : ∀ ζ : ℝ × ℤ,
      1 ≤ ENNReal.ofReal (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ) := by
    intro ζ
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (cylinderFrequencyWeight_one_le _ _ ζ)
  have h := cylinder_inverse_product_oneHigh (P := P) k s
    (fun i => measurable_cylinderFrequencyCutoffJet (P := P) (hF i) N (a i) (b i))
    (fun i => memLp_one_iff_integrable.mpr
      (integrable_cylinderFrequencyCutoffJet (P := P) (hF i)
        (memLp_one_iff_integrable.mp (hF1 i)) N (a i) (b i)))
    (fun i => cylinderFrequencyCutoffJet_memLp_two (P := P) (hF i) (hF2 i) N (a i) (b i))
    hw hw1 (fun i => (hF i).enorm) (fun i => a i + b i) hab
    (fun i ζ => enorm_cylinderFrequencyCutoffJet_le_weight (P := P) N (a i) (b i) (F i) ζ)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  apply Finset.sum_congr rfl
  intro j _
  rw [cylinder_eLpNorm_weighted_enorm (P := P) s (F j) (hF j).aestronglyMeasurable 2]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact eLpNorm_enorm (F i) (hF i).aestronglyMeasurable

end ContinuousFlexibility.Analysis
