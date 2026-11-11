import ContinuousFlexibility.Analysis.PositiveReferenceHeight

/-!
# Two-sided bounds for the constructed logarithmic reference height

The cutoffs have disjoint supports and their sum is at most one. Thus
the actual exponential blend stays between the same two positive
bounds as its endpoint heights and the middle value one. This gives
the reciprocal bound needed by the physical-to-canonical transport.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem n06_positiveEndpointCutoff_log_bounds
    {c δ B : ℝ} {h : ℝ → ℝ} (hδ : 0 < δ) (hB : 0 < B)
    (hb : ∀ x ∈ Metric.ball c δ, 1 / B ≤ h x ∧ h x ≤ B) (x : ℝ) :
    -Real.log B * positiveEndpointCutoff c δ x ≤
        positiveEndpointCutoff c δ x * Real.log (h x) ∧
      positiveEndpointCutoff c δ x * Real.log (h x) ≤
        Real.log B * positiveEndpointCutoff c δ x := by
  by_cases hx : x ∈ Metric.ball c δ
  · have hp : 0 < h x := (one_div_pos.mpr hB).trans_le (hb x hx).1
    have hl : -Real.log B ≤ Real.log (h x) := by
      rw [← Real.log_inv]
      exact Real.log_le_log (inv_pos.mpr hB) (by simpa only [one_div] using (hb x hx).1)
    have hu : Real.log (h x) ≤ Real.log B := Real.log_le_log hp (hb x hx).2
    have hη := positiveEndpointCutoff_nonneg c δ x
    constructor
    · simpa only [mul_comm (positiveEndpointCutoff c δ x)] using
        mul_le_mul_of_nonneg_left hl hη
    · simpa only [mul_comm (positiveEndpointCutoff c δ x)] using
        mul_le_mul_of_nonneg_left hu hη
  · simp only [positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hx,
      zero_mul, mul_zero, le_refl, and_self]

theorem n06_positiveReferenceHeight_bounds
    {l r δ B : ℝ} {hL hR : ℝ → ℝ} (hB : 1 ≤ B) (hδ : 0 < δ)
    (hgap : 2 * δ ≤ r - l)
    (hbL : ∀ x ∈ Metric.ball l δ, 1 / B ≤ hL x ∧ hL x ≤ B)
    (hbR : ∀ x ∈ Metric.ball r δ, 1 / B ≤ hR x ∧ hR x ≤ B) (x : ℝ) :
    1 / B ≤ positiveReferenceHeight l r δ hL hR x ∧
      positiveReferenceHeight l r δ hL hR x ≤ B ∧
      1 / positiveReferenceHeight l r δ hL hR x ≤ B := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  obtain ⟨hLL, hLU⟩ := n06_positiveEndpointCutoff_log_bounds hδ hBp hbL x
  obtain ⟨hRL, hRU⟩ := n06_positiveEndpointCutoff_log_bounds hδ hBp hbR x
  have hsum := positiveEndpointCutoff_add_le_one hδ hgap x
  have hweighted := mul_le_mul_of_nonneg_left hsum hlog
  have hl : -Real.log B ≤ positiveEndpointCutoff l δ x * Real.log (hL x) +
      positiveEndpointCutoff r δ x * Real.log (hR x) := by nlinarith
  have hu : positiveEndpointCutoff l δ x * Real.log (hL x) +
      positiveEndpointCutoff r δ x * Real.log (hR x) ≤ Real.log B := by nlinarith
  have hlow : 1 / B ≤ positiveReferenceHeight l r δ hL hR x := by
    have he := Real.exp_le_exp.mpr hl
    simpa only [Real.exp_neg, Real.exp_log hBp, one_div, positiveReferenceHeight] using he
  have hupp : positiveReferenceHeight l r δ hL hR x ≤ B := by
    have he := Real.exp_le_exp.mpr hu
    simpa only [Real.exp_log hBp, positiveReferenceHeight] using he
  refine ⟨hlow, hupp, ?_⟩
  apply (div_le_iff₀ (positiveReferenceHeight_pos l r δ hL hR x)).mpr
  have hproduct : 1 ≤ positiveReferenceHeight l r δ hL hR x * B :=
    (div_le_iff₀ hBp).mp hlow
  simpa only [mul_comm] using hproduct

end ContinuousFlexibility.Analysis
