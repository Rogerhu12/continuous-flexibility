import ContinuousFlexibility.Analysis.OneHighConvolutionComplex
import ContinuousFlexibility.Analysis.OneHighCylinderFourierInverseKernel
import Mathlib.MeasureTheory.Group.Integral

/-!
# Characters convert actual convolution to multiplication

Fubini and translation invariance prove the convolution identity directly
for arbitrary integrable complex functions. Applied to the actual cylinder
inverse character, this identifies the inverse of the full mixed convolution
with pointwise multiplication of the two inverse integrals.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal

section Group

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G]
  [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G}
  [SFinite μ] [IsAddLeftInvariant μ] [IsAddRightInvariant μ] [IsNegInvariant μ]

theorem integral_character_complexConvolution {χ : G → ℂ}
    (hχ : Measurable χ) (hχnorm : ∀ x, ‖χ x‖ = 1)
    (hχadd : ∀ x y, χ (x + y) = χ x * χ y)
    {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, χ x * complexConvolution μ f g x ∂μ) =
      (∫ x, χ x * f x ∂μ) * (∫ x, χ x * g x ∂μ) := by
  have hB : Integrable (fun p : G × G => f p.2 * g (p.1 - p.2)) (μ.prod μ) :=
    hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
  have hχB : Integrable (fun p : G × G => χ p.1 * (f p.2 * g (p.1 - p.2)))
      (μ.prod μ) :=
    hB.mono ((hχ.comp measurable_fst).aestronglyMeasurable.mul hB.aestronglyMeasurable)
      (Eventually.of_forall fun p => by
        simp only [norm_mul, hχnorm, one_mul, le_refl])
  calc
    _ = ∫ x, ∫ y, χ x * (f y * g (x - y)) ∂μ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        rw [complexConvolution_apply, integral_const_mul]
    _ = ∫ y, ∫ x, χ x * (f y * g (x - y)) ∂μ ∂μ := integral_integral_swap hχB
    _ = ∫ y, ∫ x, χ (x + y) * (f y * g x) ∂μ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simpa only [sub_add_cancel] using
          (integral_sub_right_eq_self (fun x => χ (x + y) * (f y * g x)) y (μ := μ))
    _ = ∫ y, ∫ x, (χ y * f y) * (χ x * g x) ∂μ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only
          rw [hχadd]
          ring
    _ = _ := by simp only [integral_const_mul, integral_mul_const]

end Group

variable {P : ℝ} [Fact (0 < P)]

/-- The mixed inverse of the actual complex convolution is the pointwise
product of the two mixed inverse integrals. -/
theorem cylinderFourierInverse_complexConvolution {F G : ℝ × ℤ → ℂ}
    (hF : Integrable F cylinderFrequencyMeasure)
    (hG : Integrable G cylinderFrequencyMeasure) :
    cylinderFourierInverse (P := P) (complexConvolution cylinderFrequencyMeasure F G) =
      fun p => cylinderFourierInverse F p * cylinderFourierInverse G p := by
  letI : SFinite cylinderFrequencyMeasure :=
    inferInstanceAs (SFinite ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))
  letI : IsAddLeftInvariant cylinderFrequencyMeasure :=
    inferInstanceAs (IsAddLeftInvariant ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))
  letI : IsAddRightInvariant cylinderFrequencyMeasure :=
    inferInstanceAs (IsAddRightInvariant ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))
  letI : IsNegInvariant cylinderFrequencyMeasure :=
    inferInstanceAs (IsNegInvariant ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))
  funext p
  exact integral_character_complexConvolution (μ := cylinderFrequencyMeasure)
    (measurable_cylinderInverseCharacter p) (norm_cylinderInverseCharacter p)
    (cylinderInverseCharacter_add p) hF hG

end ContinuousFlexibility.Analysis
