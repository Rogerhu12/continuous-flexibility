import ContinuousFlexibility.Radial.R11bProductSeries

/-!
# Lp limits of the original finite product sums

This interface presents the strong limit in the exact toLp form consumed by
representative selection. The functions remain the original finite sums.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped BigOperators Topology

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

theorem r11b_tensor_finset_sum_memLp
    (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (hc : ∀ n, MemLp (c n) 2 μ) (he : ∀ n, MemLp (e n) 2 ν) (s : Finset ℕ) :
    MemLp (fun z => ∑ i ∈ s, c i z.1 * e i z.2) 2 (μ.prod ν) :=
  MemLp.ae_eq (r11b_tensor_finset_sum_coeFn c e hc he s) (Lp.memLp _)

theorem r11b_tensor_finset_sum_toLp
    (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (hc : ∀ n, MemLp (c n) 2 μ) (he : ∀ n, MemLp (e n) 2 ν) (s : Finset ℕ) :
    (r11b_tensor_finset_sum_memLp c e hc he s).toLp
      (fun z => ∑ i ∈ s, c i z.1 * e i z.2) =
        ∑ i ∈ s, r11bTensorL2 (hc i) (he i) := by
  apply Lp.ext
  exact (r11b_tensor_finset_sum_memLp c e hc he s).coeFn_toLp.trans
    (r11b_tensor_finset_sum_coeFn c e hc he s).symm

theorem r11b_product_orthogonal_partialSums_tendsto
    (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (hc : ∀ n, MemLp (c n) 2 μ) (he : ∀ n, MemLp (e n) 2 ν)
    (hunit : ∀ n, (∫ y, e n y ^ 2 ∂ν) = 1)
    (horth : Pairwise (fun i j => (∫ y, e i y * e j y ∂ν) = 0))
    (hsq : Summable (fun n => ∫ x, c n x ^ 2 ∂μ)) :
    Tendsto (fun N => (r11b_tensor_finset_sum_memLp c e hc he (Finset.range N)).toLp
      (fun z => ∑ n ∈ Finset.range N, c n z.1 * e n z.2)) atTop
      (𝓝 (∑' n, r11bTensorL2 (hc n) (he n))) := by
  have hvortho : Pairwise (fun i j =>
      inner ℝ (r11bTensorL2 (hc i) (he i)) (r11bTensorL2 (hc j) (he j)) = 0) := by
    intro i j hij
    rw [r11bTensorL2_inner, horth hij, mul_zero]
  have hvsq : Summable (fun n => ‖r11bTensorL2 (hc n) (he n)‖ ^ 2) := by
    simpa only [r11bTensorL2_norm_sq, hunit, mul_one] using hsq
  have hv := (r11b_orthogonal_series_norm_sq
    (fun n => r11bTensorL2 (hc n) (he n)) hvortho hvsq).1
  simp_rw [r11b_tensor_finset_sum_toLp]
  exact hv.hasSum.tendsto_sum_nat

end ContinuousFlexibility.Radial
