import ContinuousFlexibility.Analysis.OneHighCircleFourierProduct
import ContinuousFlexibility.Analysis.OneHighConvolutionProducts

/-!
# Fourier majorants for products of any positive number of circle functions

The actual Fourier coefficients of the pointwise product are dominated by
the full positive convolution. This is the bridge from circle functions to
the arbitrary-arity one-high-factor estimate on frequency space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal MeasureTheory BigOperators

variable {P : ℝ} [Fact (0 < P)]

/-- The Fourier majorant for any positive number of actual circle factors. -/
theorem circle_enorm_fourierCoeff_prod_le_positiveConvolution (k : ℕ)
    (f : Fin (k + 1) → C(AddCircle P, ℂ))
    (hf : ∀ i, MemLp (fourierCoeff (f i)) 1 Measure.count) (n : ℤ) :
    ‖fourierCoeff (∏ i, f i) n‖ₑ ≤
      positiveConvolution Measure.count k (fun i m => ‖fourierCoeff (f i) m‖ₑ) n := by
  induction k generalizing n with
  | zero => simp only [Fin.prod_univ_one, positiveConvolution_zero, le_refl]
  | succ k ih =>
      rw [Fin.prod_univ_succ,
        positiveConvolution_succ k (fun i => measurable_of_countable _)]
      apply (circle_enorm_fourierCoeff_mul_le_lconvolution (f 0)
        (∏ i : Fin (k + 1), f i.succ) (hf 0) n).trans
      rw [lconvolution_def, lconvolution_def]
      apply lintegral_mono
      intro m
      exact mul_le_mul_of_nonneg_left
        (ih (fun i => f i.succ) (fun i => hf i.succ) (-m + n)) (by positivity)

/-- The same actual-product comparison at the `L²` frequency norm level. -/
theorem circle_eLpNorm_fourierCoeff_prod_le_positiveConvolution (k : ℕ)
    (f : Fin (k + 1) → C(AddCircle P, ℂ))
    (hf : ∀ i, MemLp (fourierCoeff (f i)) 1 Measure.count) :
    eLpNorm (fourierCoeff (∏ i, f i)) 2 Measure.count ≤
      eLpNorm (positiveConvolution Measure.count k
        (fun i m => ‖fourierCoeff (f i) m‖ₑ)) 2 Measure.count := by
  apply eLpNorm_mono_enorm (measurable_of_countable _).aestronglyMeasurable
  intro n
  simpa only [enorm_eq_self] using
    circle_enorm_fourierCoeff_prod_le_positiveConvolution k f hf n

/-- Any pointwise coefficient majorants may be inserted into the
arbitrary-arity convolution without imposing finite support. -/
theorem circle_enorm_fourierCoeff_prod_le_majorantConvolution (k : ℕ)
    (f : Fin (k + 1) → C(AddCircle P, ℂ))
    (hf : ∀ i, MemLp (fourierCoeff (f i)) 1 Measure.count)
    (b : Fin (k + 1) → ℤ → ℝ≥0∞)
    (hb : ∀ i n, ‖fourierCoeff (f i) n‖ₑ ≤ b i n) (n : ℤ) :
    ‖fourierCoeff (∏ i, f i) n‖ₑ ≤ positiveConvolution Measure.count k b n := by
  apply (circle_enorm_fourierCoeff_prod_le_positiveConvolution k f hf n).trans
  exact convolutionKernel_mono Measure.count k
    (fun ζ => Finset.prod_le_prod' (fun i _ => hb i (ζ i))) n

/-- The general one-high frequency estimate applied to an actual circle
product. Derivative coefficient identities provide the pointwise premise
in the smooth-function application. -/
theorem circle_eLpNorm_fourierCoeff_prod_le_oneHigh (k s : ℕ)
    (f : Fin (k + 1) → C(AddCircle P, ℂ))
    (hf : ∀ i, MemLp (fourierCoeff (f i)) 1 Measure.count)
    (w : ℤ → ℝ≥0∞) (hw : ∀ n, 1 ≤ w n)
    (b : Fin (k + 1) → ℤ → ℝ≥0∞)
    (a : Fin (k + 1) → ℕ) (ha : ∑ i, a i ≤ s)
    (hb : ∀ i n, ‖fourierCoeff (f i) n‖ₑ ≤ w n ^ a i * b i n) :
    eLpNorm (fourierCoeff (∏ i, f i)) 2 Measure.count ≤
      ∑ j, eLpNorm (fun n => w n ^ s * b j n) 2 Measure.count *
        ∏ i ∈ Finset.univ.erase j, eLpNorm (b i) 1 Measure.count := by
  apply le_trans ?_ (positiveConvolution_oneHigh_eLpNorm_two_le k s
    (measurable_of_countable w) hw (fun i => measurable_of_countable (b i)) a ha)
  apply eLpNorm_mono_enorm (measurable_of_countable _).aestronglyMeasurable
  intro n
  simpa only [enorm_eq_self] using
    circle_enorm_fourierCoeff_prod_le_majorantConvolution k f hf
      (fun i n => w n ^ a i * b i n) hb n

end ContinuousFlexibility.Analysis
