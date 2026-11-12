import ContinuousFlexibility.Analysis.N01cPhysicalHeightBounds

/-!
# Positive-order cutoff jets with the original height weight

The scalar cutoff is constant at the two ends. Its positive-order jets
are supported in the compact set supplied by CutoffConditions. Dividing
by any fixed positive material height weight on that compact set gives
a uniform bound, including at all higher derivative orders.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

/-- Every positive-order jet of the actual cutoff keeps the exact H
power. The zeroth jet is deliberately excluded because the cutoff is one
at the left endpoint. -/
theorem cutoff_positiveJets_le_materialHeight
    {D : ReferenceData} {T : MaterialData} {χ : ℝ → ℝ}
    (hT : IsMaterialData D T) (hχ : CutoffConditions D χ)
    (γ : ℝ) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → n ≤ s →
      ∀ r ∈ Ioo D.a D.b, |iteratedDeriv n χ r| ≤ C * T.H r ^ γ := by
  classical
  obtain ⟨K, hK, hKcore, _, hzero⟩ := hχ.2.2
  have hvanish (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∉ K) :
      iteratedDeriv n χ r = 0 := by
    cases n with
    | zero => omega
    | succ n =>
      rw [iteratedDeriv_succ']
      have he : deriv χ =ᶠ[𝓝 r] (0 : ℝ → ℝ) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hr] with t ht
        exact hzero t ht
      simpa only [iteratedDeriv_const_zero] using he.iteratedDeriv_eq n
  have hH : ContinuousOn (fun r => T.H r ^ γ) (Ioo D.a D.b) :=
    ((hT.1 T.H (by simp)).rpow_const_of_ne
      (fun r hr => (hT.2.1 r hr).2.1.ne') (p := γ)).continuousOn
  have hHp (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < T.H r ^ γ :=
    Real.rpow_pos_of_pos (hT.2.1 r hr).2.1 γ
  have hone (j : Fin (s + 1)) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo D.a D.b,
        0 < j.val → |iteratedDeriv j.val χ r| ≤ C * T.H r ^ γ := by
    have hc : Continuous (iteratedDeriv j.val χ) :=
      ContDiff.continuous_iteratedDeriv j.val hχ.1 (by simp)
    have hratio : ContinuousOn
        (fun r => |iteratedDeriv j.val χ r| / T.H r ^ γ) (Ioo D.a D.b) :=
      hc.abs.continuousOn.div hH (fun r hr => (hHp r hr).ne')
    obtain ⟨C₀, hC₀⟩ := hK.bddAbove_image (hratio.mono hKcore)
    refine ⟨max 1 C₀, zero_le_one.trans (le_max_left _ _), fun r hr hn => ?_⟩
    by_cases hrK : r ∈ K
    · apply (div_le_iff₀ (hHp r hr)).mp
      exact (hC₀ ⟨r, hrK, rfl⟩).trans (le_max_right _ _)
    · rw [hvanish j.val hn r hrK, abs_zero]
      exact mul_nonneg (zero_le_one.trans (le_max_left _ _)) (hHp r hr).le
  choose C hC hbound using hone
  let B : ℝ := ∑ j : Fin (s + 1), C j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨B, hB, fun n hn hns r hr => ?_⟩
  let j : Fin (s + 1) := ⟨n, by omega⟩
  have hCB : C j ≤ B :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)
  exact (hbound j r hr hn).trans
    (mul_le_mul_of_nonneg_right hCB (hHp r hr).le)

end ContinuousFlexibility.Statements
