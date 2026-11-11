import ContinuousFlexibility.Radial.R11bProductSeries

/-!
# Lp limits of the original finite product sums

Named raw sums and explicit toLp parameters keep elaboration independent of
the proof term used to establish membership. The limit is the tensor series.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped BigOperators Topology

set_option backward.isDefEq.respectTransparency.types false

theorem r11b_toLp_eq_of_coeFn_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) (u : Lp ℝ 2 μ)
    (huf : (u : α → ℝ) =ᵐ[μ] f) : hf.toLp f = u := by
  apply Lp.ext
  exact hf.coeFn_toLp.trans huf.symm

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

def r11bTensorFinsetSum (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (s : Finset ℕ) : α × β → ℝ :=
  fun z => ∑ i ∈ s, c i z.1 * e i z.2

def r11bTensorFinsetVector
    (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (hc : ∀ n, MemLp (c n) 2 μ) (he : ∀ n, MemLp (e n) 2 ν)
    (s : Finset ℕ) : Lp ℝ 2 (μ.prod ν) :=
  ∑ i ∈ s, r11bTensorL2 (hc i) (he i)

theorem r11b_tensor_finset_sum_memLp
    (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (hc : ∀ n, MemLp (c n) 2 μ) (he : ∀ n, MemLp (e n) 2 ν) (s : Finset ℕ) :
    MemLp (r11bTensorFinsetSum c e s) 2 (μ.prod ν) :=
  memLp_finsetSum s (fun i _ => r11b_memLp_tensor (hc i) (he i))

theorem r11b_tensor_finset_sum_toLp
    (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (hc : ∀ n, MemLp (c n) 2 μ) (he : ∀ n, MemLp (e n) 2 ν) (s : Finset ℕ) :
    MemLp.toLp (α := α × β) (E := ℝ) (p := 2) (μ := μ.prod ν)
      (r11bTensorFinsetSum c e s) (r11b_tensor_finset_sum_memLp c e hc he s) =
        r11bTensorFinsetVector c e hc he s :=
  r11b_toLp_eq_of_coeFn_ae (α := α × β) (μ := μ.prod ν)
    (f := r11bTensorFinsetSum c e s)
    (r11b_tensor_finset_sum_memLp c e hc he s)
    (r11bTensorFinsetVector c e hc he s)
    (r11b_tensor_finset_sum_coeFn c e hc he s)

theorem r11b_product_orthogonal_partialSums_tendsto
    (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (hc : ∀ n, MemLp (c n) 2 μ) (he : ∀ n, MemLp (e n) 2 ν)
    (hunit : ∀ n, (∫ y, e n y ^ 2 ∂ν) = 1)
    (horth : Pairwise (fun i j => (∫ y, e i y * e j y ∂ν) = 0))
    (hsq : Summable (fun n => ∫ x, c n x ^ 2 ∂μ)) :
    Tendsto (fun N =>
      MemLp.toLp (α := α × β) (E := ℝ) (p := 2) (μ := μ.prod ν)
        (r11bTensorFinsetSum c e (Finset.range N))
        (r11b_tensor_finset_sum_memLp c e hc he (Finset.range N))) atTop
      (𝓝 (∑' n, r11bTensorL2 (hc n) (he n))) := by
  have hvortho : Pairwise (fun i j =>
      inner ℝ (r11bTensorL2 (hc i) (he i)) (r11bTensorL2 (hc j) (he j)) = 0) := by
    intro i j hij
    rw [r11bTensorL2_inner, horth hij, mul_zero]
  have hvsq : Summable (fun n => ‖r11bTensorL2 (hc n) (he n)‖ ^ 2) := by
    simpa only [r11bTensorL2_norm_sq, hunit, mul_one] using hsq
  have hv := (r11b_orthogonal_series_norm_sq
    (fun n => r11bTensorL2 (hc n) (he n)) hvortho hvsq).1
  have hlim : Tendsto (fun N => r11bTensorFinsetVector c e hc he (Finset.range N))
      atTop (𝓝 (∑' n, r11bTensorL2 (hc n) (he n))) :=
    hv.hasSum.tendsto_sum_nat
  have hfun : (fun N =>
      MemLp.toLp (α := α × β) (E := ℝ) (p := 2) (μ := μ.prod ν)
        (r11bTensorFinsetSum c e (Finset.range N))
        (r11b_tensor_finset_sum_memLp c e hc he (Finset.range N))) =
      (fun N => r11bTensorFinsetVector c e hc he (Finset.range N)) := by
    funext N
    exact r11b_tensor_finset_sum_toLp c e hc he (Finset.range N)
  exact hfun.symm ▸ hlim

end ContinuousFlexibility.Radial
