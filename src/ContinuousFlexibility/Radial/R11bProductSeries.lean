module

public import ContinuousFlexibility.Radial.R11bOrthogonalSeries
public import ContinuousFlexibility.Radial.R11bTensorL2

/-!
# Strong reconstruction from square-summable product modes

Normalized orthogonal angular functions and square-summable radial L²
coefficients reconstruct an actual measurable product field. The raw finite
sums converge in the square-integral metric, and the limit has exactly the
sum of the radial squared norms.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped BigOperators Topology

theorem r11b_lp_norm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℝ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  simpa only [Lp.toLp_coeFn] using r11b_norm_toLp_sq (Lp.memLp u)

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

theorem r11b_tensor_finset_sum_coeFn
    (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (hc : ∀ n, MemLp (c n) 2 μ) (he : ∀ n, MemLp (e n) 2 ν) (s : Finset ℕ) :
    (⇑(∑ i ∈ s, r11bTensorL2 (hc i) (he i))) =ᵐ[μ.prod ν]
      fun z => ∑ i ∈ s, c i z.1 * e i z.2 := by
  have hall : ∀ᵐ z ∂μ.prod ν, ∀ i,
      r11bTensorL2 (hc i) (he i) z = c i z.1 * e i z.2 :=
    ae_all_iff.mpr (fun i => r11bTensorL2_coeFn (hc i) (he i))
  filter_upwards [Lp.coeFn_finsetSum s (fun i => r11bTensorL2 (hc i) (he i)), hall]
    with z hsum hz
  calc
    (∑ i ∈ s, r11bTensorL2 (hc i) (he i)) z =
        ∑ i ∈ s, r11bTensorL2 (hc i) (he i) z := by
      simpa only [Finset.sum_apply] using hsum
    _ = ∑ i ∈ s, c i z.1 * e i z.2 :=
      Finset.sum_congr rfl (fun i _ => hz i)

theorem r11b_product_orthogonal_series
    (c : ℕ → α → ℝ) (e : ℕ → β → ℝ)
    (hc : ∀ n, MemLp (c n) 2 μ) (he : ∀ n, MemLp (e n) 2 ν)
    (hunit : ∀ n, (∫ y, e n y ^ 2 ∂ν) = 1)
    (horth : Pairwise (fun i j => (∫ y, e i y * e j y ∂ν) = 0))
    (hsq : Summable (fun n => ∫ x, c n x ^ 2 ∂μ)) :
    ∃ u : α × β → ℝ, MemLp u 2 (μ.prod ν) ∧
      (∫ z, u z ^ 2 ∂μ.prod ν) = (∑' n, ∫ x, c n x ^ 2 ∂μ) ∧
      Tendsto (fun N => ∫ z, ((∑ n ∈ Finset.range N, c n z.1 * e n z.2) - u z) ^ 2
        ∂μ.prod ν) atTop (𝓝 0) := by
  let v (n : ℕ) : Lp ℝ 2 (μ.prod ν) := r11bTensorL2 (hc n) (he n)
  have hvnorm (n : ℕ) : ‖v n‖ ^ 2 = ∫ x, c n x ^ 2 ∂μ := by
    dsimp [v]
    rw [r11bTensorL2_norm_sq, hunit n, mul_one]
  have hvortho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0) := by
    intro i j hij
    dsimp [v]
    rw [r11bTensorL2_inner, horth hij, mul_zero]
  have hvsq : Summable (fun n => ‖v n‖ ^ 2) := by
    simpa only [hvnorm] using hsq
  obtain ⟨hv, hnorm⟩ := r11b_orthogonal_series_norm_sq v hvortho hvsq
  let U : Lp ℝ 2 (μ.prod ν) := ∑' n, v n
  refine ⟨U, Lp.memLp U, ?_, ?_⟩
  · calc
      (∫ z, U z ^ 2 ∂μ.prod ν) = ‖U‖ ^ 2 := (r11b_lp_norm_sq U).symm
      _ = ∑' n, ‖v n‖ ^ 2 := hnorm
      _ = ∑' n, ∫ x, c n x ^ 2 ∂μ := tsum_congr hvnorm
  · have hdiff (N : ℕ) :
        (∫ z, ((∑ n ∈ Finset.range N, c n z.1 * e n z.2) - U z) ^ 2 ∂μ.prod ν) =
          ‖(∑ n ∈ Finset.range N, v n) - U‖ ^ 2 := by
      rw [r11b_lp_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.range N, v n) U,
        r11b_tensor_finset_sum_coeFn c e hc he (Finset.range N)] with z hsub hsum
      simp only [Pi.sub_apply] at hsub
      rw [hsub, hsum]
    have hsumlim : Tendsto (fun N => ∑ n ∈ Finset.range N, v n) atTop (𝓝 U) :=
      hv.hasSum.tendsto_sum_nat
    have hlim : Tendsto (fun N => ‖(∑ n ∈ Finset.range N, v n) - U‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (hsumlim.sub_const U).norm.pow 2
    simp_rw [hdiff]
    exact hlim

end ContinuousFlexibility.Radial
