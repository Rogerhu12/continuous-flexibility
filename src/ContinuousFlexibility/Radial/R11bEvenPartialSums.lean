import ContinuousFlexibility.Radial.R11bFourierCoefficients
import ContinuousFlexibility.Radial.R11bProductSeriesLimit

/-!
# Actual finite even Fourier sums, including the mean

The index zero is the constant basis vector one. Every finite sum has exact
pointwise symmetry, and its coefficients are computed by ordinary integrals.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology

set_option backward.isDefEq.respectTransparency false

def r11bEvenPartialSum {α : Type*} (c : ℕ → α → ℝ) (N : ℕ) (z : α × ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, c n z.1 * evenCosineBasis n z.2

theorem r11bEvenPartialSum_even {α : Type*} (c : ℕ → α → ℝ) (N : ℕ) (r : α) :
    Function.Even (fun θ => r11bEvenPartialSum c N (r, θ)) := by
  intro θ
  change (∑ n ∈ Finset.range N, c n r * evenCosineBasis n (-θ)) =
    ∑ n ∈ Finset.range N, c n r * evenCosineBasis n θ
  apply Finset.sum_congr rfl
  intro n hn
  rw [evenCosineBasis_even n θ]

theorem r11bEvenPartialSum_periodic {α : Type*} (c : ℕ → α → ℝ) (N : ℕ) (r : α) :
    Function.Periodic (fun θ => r11bEvenPartialSum c N (r, θ)) Real.pi := by
  intro θ
  change (∑ n ∈ Finset.range N, c n r * evenCosineBasis n (θ + Real.pi)) =
    ∑ n ∈ Finset.range N, c n r * evenCosineBasis n θ
  apply Finset.sum_congr rfl
  intro n hn
  rw [evenCosineBasis_periodic n θ]

theorem r11bEvenPartialSum_coefficient {α : Type*}
    (c : ℕ → α → ℝ) (N n : ℕ) (r : α) :
    evenFourierCoefficient (r11bEvenPartialSum c N) n r =
      if n < N then c n r else 0 := by
  have hint (i : ℕ) :
      Integrable (fun θ => (c i r * evenCosineBasis i θ) * evenCosineBasis n θ)
        angularMeanMeasure := by
    simpa only [mul_assoc] using
      ((evenCosineBasis_memLp i).integrable_mul (evenCosineBasis_memLp n)).const_mul (c i r)
  have hterm (i : ℕ) :
      (∫ θ, (c i r * evenCosineBasis i θ) * evenCosineBasis n θ ∂angularMeanMeasure) =
        c i r * (if i = n then 1 else 0) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    rw [← angularAverage_eq_integral_angularMeanMeasure]
    exact angularPairing_evenCosineBasis i n
  rw [evenFourierCoefficient_eq_integral]
  change (∫ θ, (∑ i ∈ Finset.range N, c i r * evenCosineBasis i θ) *
    evenCosineBasis n θ ∂angularMeanMeasure) = if n < N then c n r else 0
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum (Finset.range N) (fun i _ => hint i)]
  simp_rw [hterm]
  by_cases hn : n < N
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro i hi hin
      simp [hin]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hn)).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i ≠ n := by
      intro h
      subst i
      exact hn (Finset.mem_range.mp hi)
    simp [hin]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem r11bEvenPartialSum_memLp
    (c : ℕ → α → ℝ) (hc : ∀ n, MemLp (c n) 2 μ) (N : ℕ) :
    MemLp (r11bEvenPartialSum c N) 2 (μ.prod angularMeanMeasure) :=
  r11b_tensor_finset_sum_memLp c evenCosineBasis hc evenCosineBasis_memLp (Finset.range N)

theorem r11bEvenPartialSum_tendsto
    (c : ℕ → α → ℝ) (hc : ∀ n, MemLp (c n) 2 μ)
    (hsq : Summable (fun n => ∫ r, c n r ^ 2 ∂μ)) :
    Tendsto (fun N => (r11bEvenPartialSum_memLp c hc N).toLp (r11bEvenPartialSum c N))
      atTop (𝓝 (∑' n, r11bTensorL2 (hc n) (evenCosineBasis_memLp n))) := by
  exact r11b_product_orthogonal_partialSums_tendsto c evenCosineBasis hc evenCosineBasis_memLp
    integral_sq_evenCosineBasis
    (fun _ _ hne => integral_mul_evenCosineBasis_of_ne hne) hsq

end

end ContinuousFlexibility.Radial
