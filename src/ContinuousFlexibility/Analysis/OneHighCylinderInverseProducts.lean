module

public import ContinuousFlexibility.Analysis.OneHighConvolutionComplexFinite
public import ContinuousFlexibility.Analysis.OneHighConvolutionCharacter
public import ContinuousFlexibility.Analysis.OneHighCylinderFourierInverseL2

/-!
# One-high-factor estimates for actual inverse products

These are estimates for the actual pointwise product of mixed inverse
integrals. The complex n-fold convolution is first formed as a genuine
Bochner convolution; its inverse equals the product, and the positive
convolution majorant gives the exact one-high-factor bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal BigOperators

local instance : SFinite cylinderFrequencyMeasure :=
  inferInstanceAs (SFinite ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))

local instance : IsAddLeftInvariant cylinderFrequencyMeasure :=
  inferInstanceAs (IsAddLeftInvariant ((volume : Measure ℝ).prod (Measure.count : Measure ℤ)))

variable {P : ℝ} [Fact (0 < P)]

theorem cylinderFourierInverse_complexMultipleConvolution (k : ℕ)
    {F : Fin (k + 1) → (ℝ × ℤ) → ℂ}
    (hF1 : ∀ i, MemLp (F i) 1 cylinderFrequencyMeasure) :
    cylinderFourierInverse (P := P) (complexMultipleConvolution cylinderFrequencyMeasure k F) =
      fun p => ∏ i, cylinderFourierInverse (F i) p := by
  induction k with
  | zero =>
    funext p
    rw [complexMultipleConvolution_zero]
    exact (Fin.prod_univ_one
      (fun i : Fin 1 => cylinderFourierInverse (P := P) (F i) p)).symm
  | succ k ih =>
    have ht : Integrable
        (complexMultipleConvolution cylinderFrequencyMeasure k (fun i => F i.succ))
        cylinderFrequencyMeasure :=
      memLp_one_iff_integrable.mp
        (complexMultipleConvolution_memLp_one k (fun i => hF1 i.succ))
    rw [complexMultipleConvolution_succ,
      cylinderFourierInverse_complexConvolution (memLp_one_iff_integrable.mp (hF1 0)) ht,
      ih (fun i => hF1 i.succ)]
    funext p
    exact (Fin.prod_univ_succ
      (fun i : Fin (k + 2) => cylinderFourierInverse (P := P) (F i) p)).symm

/-- Genuine physical product membership and the exact positive-convolution
majorant, for any positive number of inverse factors. -/
theorem cylinder_inverse_product_eLpNorm_two_le_majorant (k : ℕ)
    {F : Fin (k + 1) → (ℝ × ℤ) → ℂ}
    (hF : ∀ i, Measurable (F i))
    (hF1 : ∀ i, MemLp (F i) 1 cylinderFrequencyMeasure)
    (hF2 : ∀ i, MemLp (F i) 2 cylinderFrequencyMeasure)
    (b : Fin (k + 1) → (ℝ × ℤ) → ℝ≥0∞)
    (hb : ∀ i ζ, ‖F i ζ‖ₑ ≤ b i ζ) :
    MemLp (fun p : ℝ × AddCircle P => ∏ i, cylinderFourierInverse (F i) p)
      2 (cylinderPhysicalMeasure P) ∧
    eLpNorm (fun p : ℝ × AddCircle P => ∏ i, cylinderFourierInverse (F i) p)
      2 (cylinderPhysicalMeasure P) ≤
        eLpNorm (positiveConvolution cylinderFrequencyMeasure k b) 2 cylinderFrequencyMeasure := by
  let H := complexMultipleConvolution cylinderFrequencyMeasure k F
  have hHm : Measurable H := measurable_complexMultipleConvolution k hF
  have hH1 : Integrable H cylinderFrequencyMeasure :=
    memLp_one_iff_integrable.mp (complexMultipleConvolution_memLp_one k hF1)
  have hH2 : MemLp H 2 cylinderFrequencyMeasure := complexMultipleConvolution_memLp_two k hF1 hF2
  have he := cylinderFourierInverse_complexMultipleConvolution (P := P) k hF1
  constructor
  · rw [← he]
    exact cylinderFourierInverse_memLp_two hHm hH1 hH2
  · rw [← he, cylinderFourierInverse_eLpNorm_two hHm hH1 hH2]
    exact complexMultipleConvolution_eLpNorm_two_le_majorant k hF b hb

/-- The arbitrary-arity one-high estimate for actual inverse products.
The displayed multiplier majorants are pointwise frequency bounds, not
assumed product norm estimates. -/
theorem cylinder_inverse_product_oneHigh (k s : ℕ)
    {F : Fin (k + 1) → (ℝ × ℤ) → ℂ}
    (hF : ∀ i, Measurable (F i))
    (hF1 : ∀ i, MemLp (F i) 1 cylinderFrequencyMeasure)
    (hF2 : ∀ i, MemLp (F i) 2 cylinderFrequencyMeasure)
    {w : ℝ × ℤ → ℝ≥0∞} (hw : Measurable w) (hw1 : ∀ ζ, 1 ≤ w ζ)
    {b : Fin (k + 1) → (ℝ × ℤ) → ℝ≥0∞} (hb : ∀ i, Measurable (b i))
    (a : Fin (k + 1) → ℕ) (ha : ∑ i, a i ≤ s)
    (hbound : ∀ i ζ, ‖F i ζ‖ₑ ≤ w ζ ^ a i * b i ζ) :
    MemLp (fun p : ℝ × AddCircle P => ∏ i, cylinderFourierInverse (F i) p)
      2 (cylinderPhysicalMeasure P) ∧
    eLpNorm (fun p : ℝ × AddCircle P => ∏ i, cylinderFourierInverse (F i) p)
      2 (cylinderPhysicalMeasure P) ≤
      ∑ j, eLpNorm (fun ζ => w ζ ^ s * b j ζ) 2 cylinderFrequencyMeasure *
        ∏ i ∈ Finset.univ.erase j, eLpNorm (b i) 1 cylinderFrequencyMeasure := by
  have h := cylinder_inverse_product_eLpNorm_two_le_majorant (P := P) k hF hF1 hF2
    (fun i ζ => w ζ ^ a i * b i ζ) hbound
  exact ⟨h.1, h.2.trans (positiveConvolution_oneHigh_eLpNorm_two_le
    (μ := cylinderFrequencyMeasure) k s hw hw1 hb a ha)⟩

end ContinuousFlexibility.Analysis
