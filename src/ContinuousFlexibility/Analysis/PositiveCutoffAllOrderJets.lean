module

public import ContinuousFlexibility.Analysis.N06PositiveCutoffJets

/-!
# All orders after the same actual endpoint cutoff

The cutoff width is supplied once. Its inverse controls only the fixed
cutoff factor, while the actual local endpoint jet envelope remains
linear. Outside the supplied collar the genuine zero germ removes all
regularity requirements on the endpoint field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff BigOperators

/-- The same chosen cutoff works at every requested order. In
particular, the high-order envelope M does not determine its width. -/
theorem exists_positiveEndpointCutoff_mul_jet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {δ U M : ℝ},
      0 < δ → 1 ≤ U → δ⁻¹ ≤ U → 0 ≤ M →
      ∀ (c : ℝ) (f : ℝ → ℝ),
        (∀ x ∈ Metric.ball c δ, ContDiffAt ℝ ∞ f x) →
        (∀ k, k ≤ N → ∀ x ∈ Metric.ball c δ, |iteratedDeriv k f x| ≤ M) →
        ∀ k, k ≤ N → ∀ x : ℝ,
          |iteratedDeriv k (fun t => positiveEndpointCutoff c δ t * f t) x| ≤
            C * U ^ N * M := by
  classical
  choose A hA hcut using n06_positiveEndpointCutoff_jet_bound
  let B : ℕ → ℝ := fun k =>
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A j
  have hB (k : ℕ) : 0 ≤ B k :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (hA j))
  let C : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), B k
  have hC : 1 ≤ C := by
    have hs : 0 ≤ ∑ k ∈ Finset.range (N + 1), B k :=
      Finset.sum_nonneg fun k _ => hB k
    dsimp only [C]
    linarith only [hs]
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hBC (k : ℕ) (hk : k ≤ N) : B k ≤ C := by
    have hs := Finset.single_le_sum (fun j _ => hB j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    exact hs.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro δ U M hδ hU hδU hM c f hf hfb k hk x
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hUpow : 0 ≤ U ^ N := pow_nonneg hU0 N
  by_cases hx : x ∈ Metric.ball c δ
  · have hcutbound (j : ℕ) (hj : j ≤ k) :
        |iteratedDeriv j (positiveEndpointCutoff c δ) x| ≤ A j * U ^ N := by
      have hpower : δ⁻¹ ^ j ≤ U ^ N :=
        (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδU j).trans
          (pow_le_pow_right₀ hU (hj.trans hk))
      exact (hcut j c δ x hδ).trans
        (mul_le_mul_of_nonneg_left hpower (zero_le_one.trans (hA j)))
    rw [iteratedDeriv_fun_mul
      (((contDiff_positiveEndpointCutoff c δ).of_le
        (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
      ((hf x hx).of_le (show (k : ℕ∞ω) ≤ ∞ by simp))]
    calc
      _ ≤ ∑ j ∈ Finset.range (k + 1),
          |(k.choose j : ℝ) * iteratedDeriv j (positiveEndpointCutoff c δ) x *
            iteratedDeriv (k - j) f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (k + 1),
          ((k.choose j : ℝ) * A j) * U ^ N * M := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        have hprod := mul_le_mul (hcutbound j hjk)
          (hfb (k - j) ((Nat.sub_le k j).trans hk) x hx)
          (abs_nonneg _) (mul_nonneg (zero_le_one.trans (hA j)) hUpow)
        have he := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg (k.choose j))
        exact (by simpa only [mul_assoc] using he)
      _ = B k * U ^ N * M := by
        dsimp only [B]
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ C * U ^ N * M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hBC k hk) hUpow) hM
  · have he : (fun t => positiveEndpointCutoff c δ t * f t) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ hx] with t ht
      simp only [ht, Pi.zero_apply, zero_mul]
    rw [he.iteratedDeriv_eq k, iteratedDeriv_fun_const_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC0 hUpow) hM

end ContinuousFlexibility.Analysis
