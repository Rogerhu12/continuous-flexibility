module

public import ContinuousFlexibility.Analysis.N06PositiveCutoffJets

/-!
# Finite jets of locally defined endpoint fields after clipping

The endpoint slope and logarithmic height need only be smooth on their
actual collar. Multiplication by the fixed cutoff gives a global smooth
field. The first two derivative bounds follow from the real product
rule on that collar and the zero germ outside it.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n06_scalarJetTwoBound_iff {f : ℝ → ℝ} {x B : ℝ} :
    N06ScalarJetTwoBound f x B ↔ ∀ k : ℕ, k ≤ 2 → |iteratedDeriv k f x| ≤ B := by
  constructor
  · intro h k hk
    interval_cases k
    · simpa only [iteratedDeriv_zero] using h.value
    · simpa only [iteratedDeriv_one] using h.first
    · simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_zero] using h.second
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [iteratedDeriv_zero] using h 0 (by norm_num)
    · simpa only [iteratedDeriv_one] using h 1 (by norm_num)
    · simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_zero] using h 2 (by norm_num)

theorem N06ScalarJetTwoBound.add_at
    {f g : ℝ → ℝ} {x B C : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hfb : N06ScalarJetTwoBound f x B) (hgb : N06ScalarJetTwoBound g x C) :
    N06ScalarJetTwoBound (fun t => f t + g t) x (B + C) := by
  apply n06_scalarJetTwoBound_iff.mpr
  intro k hk
  rw [iteratedDeriv_fun_add (hf.of_le (by simp)) (hg.of_le (by simp))]
  exact (abs_add_le _ _).trans (add_le_add
    (n06_scalarJetTwoBound_iff.mp hfb k hk) (n06_scalarJetTwoBound_iff.mp hgb k hk))

theorem N06ScalarJetTwoBound.sub_at
    {f g : ℝ → ℝ} {x B C : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hfb : N06ScalarJetTwoBound f x B) (hgb : N06ScalarJetTwoBound g x C) :
    N06ScalarJetTwoBound (fun t => f t - g t) x (B + C) := by
  apply n06_scalarJetTwoBound_iff.mpr
  intro k hk
  rw [iteratedDeriv_fun_sub (hf.of_le (by simp)) (hg.of_le (by simp))]
  have habs : |iteratedDeriv k f x - iteratedDeriv k g x| ≤
      |iteratedDeriv k f x| + |iteratedDeriv k g x| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (iteratedDeriv k f x) 0 (iteratedDeriv k g x)
  exact habs.trans (add_le_add
    (n06_scalarJetTwoBound_iff.mp hfb k hk) (n06_scalarJetTwoBound_iff.mp hgb k hk))

theorem N06ScalarJetTwoBound.const_mul
    {f : ℝ → ℝ} {x B : ℝ} (hfb : N06ScalarJetTwoBound f x B) (c : ℝ) :
    N06ScalarJetTwoBound (fun t => c * f t) x (|c| * B) := by
  apply n06_scalarJetTwoBound_iff.mpr
  intro k hk
  rw [iteratedDeriv_const_mul_field, abs_mul]
  exact mul_le_mul_of_nonneg_left (n06_scalarJetTwoBound_iff.mp hfb k hk) (abs_nonneg c)

theorem N06ScalarJetTwoBound.mul_at
    {f g : ℝ → ℝ} {x B C : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfb : N06ScalarJetTwoBound f x B) (hgb : N06ScalarJetTwoBound g x C) :
    N06ScalarJetTwoBound (fun t => f t * g t) x (4 * B * C) := by
  have hmul {u v : ℝ} (hu : |u| ≤ B) (hv : |v| ≤ C) : |u * v| ≤ B * C := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg v) hB
  have hBC := mul_nonneg hB hC
  have hsecond : deriv (deriv (fun t => f t * g t)) x =
      f x * deriv (deriv g) x + 2 * (deriv f x * deriv g x) +
        deriv (deriv f) x * g x := by
    have he := iteratedDeriv_fun_mul (n := 2) (hf.of_le (by simp)) (hg.of_le (by simp))
    norm_num [Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero] at he
    exact he.trans (by ring)
  constructor
  · exact (hmul hfb.value hgb.value).trans (by nlinarith)
  · rw [deriv_fun_mul (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))]
    have he := (abs_add_le _ _).trans
      (add_le_add (hmul hfb.first hgb.value) (hmul hfb.value hgb.first))
    nlinarith
  · rw [hsecond]
    have hmiddle : |2 * (deriv f x * deriv g x)| ≤ 2 * (B * C) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (hmul hfb.first hgb.first) (by norm_num)
    have he := (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (hmul hfb.value hgb.second) hmiddle))
      (hmul hfb.second hgb.value))
    nlinarith

/-- No regularity of the endpoint field is imposed beyond the actual
collar. The cutoff is zero on a neighborhood of each excluded point. -/
theorem n06_positiveEndpointCutoff_mul_twoJet
    {c δ B C : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ x ∈ Metric.ball c δ, ContDiffAt ℝ ∞ f x)
    (hfb : ∀ x ∈ Metric.ball c δ, N06ScalarJetTwoBound f x B)
    (hcut : ∀ x, N06ScalarJetTwoBound (positiveEndpointCutoff c δ) x C) (x : ℝ) :
    N06ScalarJetTwoBound (fun t => positiveEndpointCutoff c δ t * f t) x (4 * C * B) := by
  by_cases hx : x ∈ Metric.ball c δ
  · exact (hcut x).mul_at (contDiff_positiveEndpointCutoff c δ).contDiffAt
      (hf x hx) hC hB (hfb x hx)
  · have he : (fun t => positiveEndpointCutoff c δ t * f t) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ hx] with t ht
      simp only [ht, Pi.zero_apply, zero_mul]
    apply n06_scalarJetTwoBound_iff.mpr
    intro k _
    rw [he.iteratedDeriv_eq k, iteratedDeriv_fun_const_zero, abs_zero]
    positivity

end ContinuousFlexibility.Analysis
