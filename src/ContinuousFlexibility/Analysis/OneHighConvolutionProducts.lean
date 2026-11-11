import ContinuousFlexibility.Analysis.OneHighConvolutionFinite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Arbitrary-arity one-high-factor frequency estimates

The product of nonnegative powers of weights at least one is bounded by the sum
of the weights raised to the total allowed order. Applying this inside the
actual convolution integral, and then Young's inequality, gives exactly one
weighted `L²` factor in each term and unweighted `L¹` norms for every other factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal MeasureTheory BigOperators

/-- The elementary frequency inequality for any nonempty family of weights. -/
theorem prod_frequencyWeights_le_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ≥0∞) (a : ι → ℕ) (s : ℕ)
    (hw : ∀ i, 1 ≤ w i) (ha : ∑ i, a i ≤ s) :
    (∏ i, w i ^ a i) ≤ ∑ i, w i ^ s := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty w
  have hmax (i : ι) : w i ≤ w j := by
    rw [← hj]
    exact Finset.le_sup (Finset.mem_univ i)
  calc
    (∏ i, w i ^ a i) ≤ ∏ i, w j ^ a i :=
      Finset.prod_le_prod' (fun i _ => pow_le_pow_left₀ zero_le (hmax i) (a i))
    _ = w j ^ (∑ i, a i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ w j ^ s := pow_le_pow_right₀ (hw j) ha
    _ ≤ ∑ i, w i ^ s :=
      Finset.single_le_sum (f := fun i => w i ^ s) (fun i _ => zero_le) (Finset.mem_univ j)

theorem prod_weighted_frequency_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (w : ι → ℝ≥0∞) (a : ι → ℕ) (s : ℕ) (u : ι → ℝ≥0∞)
    (hw : ∀ i, 1 ≤ w i) (ha : ∑ i, a i ≤ s) :
    (∏ i, w i ^ a i * u i) ≤
      ∑ j, ∏ i, (if i = j then w i ^ s else 1) * u i := by
  classical
  rw [Finset.prod_mul_distrib]
  calc
    (∏ i, w i ^ a i) * (∏ i, u i) ≤ (∑ j, w j ^ s) * (∏ i, u i) :=
      mul_le_mul_of_nonneg_right (prod_frequencyWeights_le_sum w a s hw ha) zero_le
    _ = ∑ j, w j ^ s * (∏ i, u i) := Finset.sum_mul _ _ _
    _ = ∑ j, ∏ i, (if i = j then w i ^ s else 1) * u i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G]
  [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ]

/-- A family with precisely its distinguished factor carrying the full order. -/
def oneHighFrequencyFamily {k : ℕ} (w : G → ℝ≥0∞) (s : ℕ)
    (f : Fin (k + 1) → G → ℝ≥0∞) (j i : Fin (k + 1)) : G → ℝ≥0∞ :=
  fun x => if i = j then w x ^ s * f i x else f i x

theorem measurable_oneHighFrequencyFamily {k : ℕ} {w : G → ℝ≥0∞} {s : ℕ}
    {f : Fin (k + 1) → G → ℝ≥0∞} (hw : Measurable w) (hf : ∀ i, Measurable (f i))
    (j i : Fin (k + 1)) : Measurable (oneHighFrequencyFamily w s f j i) := by
  classical
  by_cases hij : i = j
  · have he : oneHighFrequencyFamily w s f j i = (fun x => w x ^ s * f i x) := by
      funext x
      simp only [oneHighFrequencyFamily, if_pos hij]
    rw [he]
    exact (hw.pow_const s).mul (hf i)
  · have he : oneHighFrequencyFamily w s f j i = f i := by
      funext x
      simp only [oneHighFrequencyFamily, if_neg hij]
    rw [he]
    exact hf i

/-- The one-high-factor inequality holds already at each output frequency. -/
theorem positiveConvolution_oneHigh_le (k s : ℕ) {w : G → ℝ≥0∞}
    {f : Fin (k + 1) → G → ℝ≥0∞} (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (hf : ∀ i, Measurable (f i)) (a : Fin (k + 1) → ℕ) (ha : ∑ i, a i ≤ s) (x : G) :
    positiveConvolution μ k (fun i y => w y ^ a i * f i y) x ≤
      ∑ j, positiveConvolution μ k (oneHighFrequencyFamily w s f j) x := by
  classical
  have hpoint (ζ : Fin (k + 1) → G) :
      (∏ i, w (ζ i) ^ a i * f i (ζ i)) ≤
        ∑ j, ∏ i, oneHighFrequencyFamily w s f j i (ζ i) := by
    simpa only [oneHighFrequencyFamily, ite_mul, one_mul] using
      prod_weighted_frequency_le_sum (fun i => w (ζ i)) a s (fun i => f i (ζ i))
        (fun i => hw1 (ζ i)) ha
  calc
    _ ≤ convolutionKernel μ k
        (fun ζ => ∑ j, ∏ i, oneHighFrequencyFamily w s f j i (ζ i)) x :=
      convolutionKernel_mono μ k hpoint x
    _ = _ := convolutionKernel_finset_sum k Finset.univ _ (fun j _ =>
      Finset.univ.measurable_fun_prod (fun i _ =>
        (measurable_oneHighFrequencyFamily hw hf j i).comp (measurable_pi_apply i))) x

variable [IsAddLeftInvariant μ] [IsNegInvariant μ]

/-- The full arbitrary-positive-arity one-high-factor convolution estimate.
The constant is one in the frequency normalization used here. -/
theorem positiveConvolution_oneHigh_eLpNorm_two_le (k s : ℕ) {w : G → ℝ≥0∞}
    {f : Fin (k + 1) → G → ℝ≥0∞} (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (hf : ∀ i, Measurable (f i)) (a : Fin (k + 1) → ℕ) (ha : ∑ i, a i ≤ s) :
    eLpNorm (positiveConvolution μ k (fun i y => w y ^ a i * f i y)) 2 μ ≤
      ∑ j, eLpNorm (fun y => w y ^ s * f j y) 2 μ *
        ∏ i ∈ Finset.univ.erase j, eLpNorm (f i) 1 μ := by
  classical
  have hm : Measurable (positiveConvolution μ k (fun i y => w y ^ a i * f i y)) :=
    measurable_positiveConvolution k (fun i => (hw.pow_const (a i)).mul (hf i))
  have hhigh (j : Fin (k + 1)) :
      eLpNorm (positiveConvolution μ k (oneHighFrequencyFamily w s f j)) 2 μ ≤
        eLpNorm (fun y => w y ^ s * f j y) 2 μ *
          ∏ i ∈ Finset.univ.erase j, eLpNorm (f i) 1 μ := by
    have h := positiveConvolution_eLpNorm_two_le (μ := μ) k
      (f := oneHighFrequencyFamily w s f j)
      (measurable_oneHighFrequencyFamily (s := s) hw hf j) j
    have hhead : oneHighFrequencyFamily w s f j j = (fun y => w y ^ s * f j y) := by
      funext y
      simp only [oneHighFrequencyFamily, ite_true]
    have hprod :
        (∏ i ∈ Finset.univ.erase j, eLpNorm (oneHighFrequencyFamily w s f j i) 1 μ) =
          ∏ i ∈ Finset.univ.erase j, eLpNorm (f i) 1 μ := by
      apply Finset.prod_congr rfl
      intro i hi
      have hij := (Finset.mem_erase.mp hi).1
      have he : oneHighFrequencyFamily w s f j i = f i := by
        funext y
        simp only [oneHighFrequencyFamily, if_neg hij]
      rw [he]
    rwa [hhead, hprod] at h
  calc
    _ ≤ eLpNorm (fun x => ∑ j,
        positiveConvolution μ k (oneHighFrequencyFamily w s f j) x) 2 μ :=
      eLpNorm_mono_enorm_ae hm.aestronglyMeasurable <| Filter.Eventually.of_forall fun x => by
        simpa only [enorm_eq_self] using
          positiveConvolution_oneHigh_le (μ := μ) k s hw hw1 hf a ha x
    _ ≤ ∑ j, eLpNorm (positiveConvolution μ k (oneHighFrequencyFamily w s f j)) 2 μ := by
      have hsum : (∑ j : Fin (k + 1), positiveConvolution μ k (oneHighFrequencyFamily w s f j)) =
          (fun x => ∑ j : Fin (k + 1),
            positiveConvolution μ k (oneHighFrequencyFamily w s f j) x) := by
        funext x
        simp only [Finset.sum_apply]
      rw [← hsum]
      exact eLpNorm_sum_le
        (f := fun j => positiveConvolution μ k (oneHighFrequencyFamily w s f j))
        (s := Finset.univ) (μ := μ) (p := (2 : ℝ≥0∞)) (by norm_num)
    _ ≤ _ := Finset.sum_le_sum (fun j _ => hhigh j)

/-- Finite endpoint norms guarantee actual `L²` membership of the convolution
with the derivatives distributed among its factors. -/
theorem positiveConvolution_oneHigh_memLp_two (k s : ℕ) {w : G → ℝ≥0∞}
    {f : Fin (k + 1) → G → ℝ≥0∞} (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (hf : ∀ i, Measurable (f i)) (a : Fin (k + 1) → ℕ) (ha : ∑ i, a i ≤ s)
    (hlow : ∀ i, MemLp (f i) 1 μ)
    (hhigh : ∀ i, MemLp (fun y => w y ^ s * f i y) 2 μ) :
    MemLp (positiveConvolution μ k (fun i y => w y ^ a i * f i y)) 2 μ := by
  apply memLp_iff.mpr
  apply (positiveConvolution_oneHigh_eLpNorm_two_le (μ := μ) k s hw hw1 hf a ha).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro j _
  exact ENNReal.mul_lt_top (hhigh j) (ENNReal.prod_lt_top (fun i _ => hlow i))

end ContinuousFlexibility.Analysis
