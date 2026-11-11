import ContinuousFlexibility.Analysis.OneHighConvolutionKernel
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Young's inequality for any positive number of factors

Every distinguished factor can occupy the `L²` position; all remaining factors
contribute their `L¹` norms. No restriction on the location of the high factor
or on the supports of the frequency functions is imposed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal MeasureTheory BigOperators

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G]
  [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G}
  [SFinite μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

theorem lconvolution_eLpNorm_one {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆ₗ[μ] g) 1 μ = eLpNorm f 1 μ * eLpNorm g 1 μ := by
  rw [eLpNorm_one_eq_lintegral_enorm (aemeasurable_lconvolution hf hg).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
  simpa only [enorm_eq_self] using lconvolution_lintegral hf hg

theorem positiveConvolution_eLpNorm_one (k : ℕ) {f : Fin (k + 1) → G → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    eLpNorm (positiveConvolution μ k f) 1 μ = ∏ i, eLpNorm (f i) 1 μ := by
  induction k generalizing f with
  | zero => simp only [positiveConvolution_zero, Fin.prod_univ_one]
  | succ k ih =>
    rw [positiveConvolution_succ k hf,
      lconvolution_eLpNorm_one (hf 0).aemeasurable
        (measurable_positiveConvolution k (fun i => hf i.succ)).aemeasurable,
      ih (fun i => hf i.succ), Fin.prod_univ_succ]

private theorem positiveConvolution_two_le_product (k : ℕ)
    {f : Fin (k + 1) → G → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (j : Fin (k + 1)) :
    eLpNorm (positiveConvolution μ k f) 2 μ ≤
      ∏ i, if i = j then eLpNorm (f i) 2 μ else eLpNorm (f i) 1 μ := by
  classical
  induction k generalizing f with
  | zero =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [positiveConvolution_zero, Fin.prod_univ_one, ite_true, le_refl]
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [positiveConvolution_succ k hf, Fin.prod_univ_succ]
      simp only [ite_true, Fin.succ_ne_zero, ite_false]
      calc
        _ ≤ eLpNorm (f 0) 2 μ *
            eLpNorm (positiveConvolution μ k (fun i => f i.succ)) 1 μ :=
          lconvolution_eLpNorm_two_le' (hf 0).aemeasurable
            (measurable_positiveConvolution k (fun i => hf i.succ)).aemeasurable
        _ = _ := by rw [positiveConvolution_eLpNorm_one k (fun i => hf i.succ)]
    · rw [positiveConvolution_succ k hf, Fin.prod_univ_succ]
      simp only [Fin.zero_ne_succ, Fin.succ_inj, ite_false]
      exact (lconvolution_eLpNorm_two_le (hf 0).aemeasurable
        (measurable_positiveConvolution k (fun i => hf i.succ)).aemeasurable).trans
          (mul_le_mul_left' (ih (fun i => hf i.succ) j) _)

/-- The arbitrary-position, arbitrary-positive-arity Young estimate. -/
theorem positiveConvolution_eLpNorm_two_le (k : ℕ)
    {f : Fin (k + 1) → G → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (j : Fin (k + 1)) :
    eLpNorm (positiveConvolution μ k f) 2 μ ≤
      eLpNorm (f j) 2 μ * ∏ i ∈ Finset.univ.erase j, eLpNorm (f i) 1 μ := by
  classical
  have h := positiveConvolution_two_le_product k hf j
  have hprod : (∏ i, if i = j then eLpNorm (f i) 2 μ else eLpNorm (f i) 1 μ) =
      eLpNorm (f j) 2 μ * ∏ i ∈ Finset.univ.erase j, eLpNorm (f i) 1 μ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact if_neg (Finset.mem_erase.mp hi).1
  rwa [hprod] at h

end ContinuousFlexibility.Analysis
