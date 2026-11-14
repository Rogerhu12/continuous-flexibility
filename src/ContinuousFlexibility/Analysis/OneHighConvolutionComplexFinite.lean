module

public import ContinuousFlexibility.Analysis.OneHighConvolutionComplex
public import ContinuousFlexibility.Analysis.OneHighConvolutionProducts

/-!
# Actual complex convolution of any positive number of factors

The recursive Bochner convolution is measurable and belongs to L1 and L2
under the corresponding genuine endpoint memberships. Its extended norm
is bounded by the full positive convolution, including for arbitrary
pointwise nonnegative majorants.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal BigOperators

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G]
  [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G}
  [SFinite μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

def complexMultipleConvolution (μ : Measure G) :
    (k : ℕ) → (Fin (k + 1) → G → ℂ) → G → ℂ
  | 0, f => f 0
  | k + 1, f => complexConvolution μ (f 0)
      (complexMultipleConvolution μ k (fun i => f i.succ))

@[simp] theorem complexMultipleConvolution_zero (f : Fin 1 → G → ℂ) :
    complexMultipleConvolution μ 0 f = f 0 := rfl

theorem complexMultipleConvolution_succ (k : ℕ) (f : Fin (k + 2) → G → ℂ) :
    complexMultipleConvolution μ (k + 1) f =
      complexConvolution μ (f 0) (complexMultipleConvolution μ k (fun i => f i.succ)) := rfl

theorem measurable_complexMultipleConvolution (k : ℕ)
    {f : Fin (k + 1) → G → ℂ} (hf : ∀ i, Measurable (f i)) :
    Measurable (complexMultipleConvolution μ k f) := by
  induction k with
  | zero => exact hf 0
  | succ k ih =>
    exact measurable_complexConvolution (hf 0) (ih (fun i => hf i.succ))

theorem complexMultipleConvolution_memLp_one (k : ℕ)
    {f : Fin (k + 1) → G → ℂ} (hf : ∀ i, MemLp (f i) 1 μ) :
    MemLp (complexMultipleConvolution μ k f) 1 μ := by
  induction k with
  | zero => exact hf 0
  | succ k ih => exact complexConvolution_memLp_one (hf 0) (ih (fun i => hf i.succ))

theorem complexMultipleConvolution_memLp_two (k : ℕ)
    {f : Fin (k + 1) → G → ℂ}
    (hf1 : ∀ i, MemLp (f i) 1 μ) (hf2 : ∀ i, MemLp (f i) 2 μ) :
    MemLp (complexMultipleConvolution μ k f) 2 μ := by
  induction k with
  | zero => exact hf2 0
  | succ k ih =>
    exact complexConvolution_memLp_two (hf1 0)
      (ih (fun i => hf1 i.succ) (fun i => hf2 i.succ))

theorem enorm_complexMultipleConvolution_le (k : ℕ)
    {f : Fin (k + 1) → G → ℂ} (hf : ∀ i, Measurable (f i)) :
    ∀ x : G, ‖complexMultipleConvolution μ k f x‖ₑ ≤
      positiveConvolution μ k (fun i y => ‖f i y‖ₑ) x := by
  induction k with
  | zero =>
    intro x
    simpa only [complexMultipleConvolution_zero, positiveConvolution_zero] using
      (le_refl ‖f 0 x‖ₑ)
  | succ k ih =>
    intro x
    rw [complexMultipleConvolution_succ, positiveConvolution_succ k (fun i => (hf i).enorm)]
    refine (enorm_complexConvolution_le (μ := μ) (f 0)
      (complexMultipleConvolution μ k (fun i => f i.succ)) x).trans ?_
    rw [lconvolution_def, lconvolution_def]
    apply lintegral_mono
    intro y
    exact mul_le_mul_of_nonneg_left (ih (fun i => hf i.succ) (-y + x)) zero_le

theorem complexMultipleConvolution_eLpNorm_two_le_majorant (k : ℕ)
    {f : Fin (k + 1) → G → ℂ} (hf : ∀ i, Measurable (f i))
    (b : Fin (k + 1) → G → ℝ≥0∞) (hb : ∀ i x, ‖f i x‖ₑ ≤ b i x) :
    eLpNorm (complexMultipleConvolution μ k f) 2 μ ≤
      eLpNorm (positiveConvolution μ k b) 2 μ := by
  apply eLpNorm_mono_enorm_ae (measurable_complexMultipleConvolution (μ := μ) k hf).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [enorm_eq_self]
    refine (enorm_complexMultipleConvolution_le (μ := μ) k hf x).trans ?_
    exact convolutionKernel_mono μ k
      (fun ζ => Finset.prod_le_prod' (fun i _ => hb i (ζ i))) x

end ContinuousFlexibility.Analysis
