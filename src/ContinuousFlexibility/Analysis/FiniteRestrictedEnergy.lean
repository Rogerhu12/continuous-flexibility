module

public import ContinuousFlexibility.Analysis.RestrictedOverlapEnergy
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite jet estimates inside an actual measurable support

A pointwise squared estimate on the full support gives the corresponding
L2 energy estimate without replacing a local energy by a global norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem eLpNorm_sq_le_finset_restricted_energy
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {A : Set α} {f : α → ℝ} {g : ι → α → ℝ} {K : ℝ}
    (hA : MeasurableSet A) (hK : 0 ≤ K)
    (hf : AEStronglyMeasurable f μ)
    (hg : ∀ i ∈ s, AEStronglyMeasurable (g i) μ)
    (hzero : ∀ x, x ∉ A → f x = 0)
    (hbound : ∀ x ∈ A, |f x| ^ 2 ≤ K * ∑ i ∈ s, |g i x| ^ 2) :
    eLpNorm f 2 μ ^ 2 ≤
      ENNReal.ofReal K * ∑ i ∈ s, eLpNorm (g i) 2 (μ.restrict A) ^ 2 := by
  classical
  have hsupp : Function.support f ⊆ A := by
    intro x hx
    by_contra hnot
    exact hx (hzero x hnot)
  have hpoint (x : α) (hx : x ∈ A) :
      ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal K * ∑ i ∈ s, ‖g i x‖ₑ ^ 2 := by
    calc
      _ = ENNReal.ofReal (|f x| ^ 2) := by
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
      _ ≤ ENNReal.ofReal (K * ∑ i ∈ s, |g i x| ^ 2) :=
        ENNReal.ofReal_le_ofReal (hbound x hx)
      _ = _ := by
        rw [ENNReal.ofReal_mul hK,
          ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (|g i x|))]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
  rw [← eLpNorm_restrict_eq_of_support_subset hf hsupp,
    eLpNorm_two_sq_eq_lintegral_of_aestronglyMeasurable hf.restrict]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal K * ∑ i ∈ s, ‖g i x‖ₑ ^ 2 ∂μ.restrict A := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      exact hpoint x hx
    _ = ENNReal.ofReal K * ∑ i ∈ s, ∫⁻ x, ‖g i x‖ₑ ^ 2 ∂μ.restrict A := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum' s (fun i hi => ((hg i hi).restrict.enorm).pow_const (2 : ℕ))]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (eLpNorm_two_sq_eq_lintegral_of_aestronglyMeasurable
        (hg i hi).restrict).symm

end ContinuousFlexibility.Statements
