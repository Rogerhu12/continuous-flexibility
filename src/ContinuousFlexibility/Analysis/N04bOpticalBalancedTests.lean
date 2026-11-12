import ContinuousFlexibility.Analysis.N04bCutVariationTests

/-!
# Balanced optical first-variation tests

This module converts the compact tests of `N04bCutVariationTests` to the
interval-integral convention used for optical travel. It reuses the same
test construction on both sides of the cut.

Only continuity of the weight is needed. In the optical application its
vanishing at both roots and positivity at the cut give the two endpoint
inequalities. These results concern the test functions, without assuming a
canonical chart or asserting the full N04b statement or its negation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- A compactly supported derivative can be integrated on its enclosing
interval instead of the whole line. -/
theorem n04b_integral_weighted_deriv_eq_interval {a b : ℝ} (hab : a ≤ b)
    (weight f : ℝ → ℝ) (hs : tsupport f ⊆ Ioo a b) :
    (∫ x, weight x * deriv f x) = ∫ x in a..b, weight x * deriv f x := by
  rw [intervalIntegral.integral_of_le hab]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hd : deriv f x = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => hx ⟨(hs (tsupport_deriv_subset hh)).1,
      (hs (tsupport_deriv_subset hh)).2.le⟩)
  rw [hd, mul_zero]

/-- At every interior cut, a continuous weight vanishing at both outer
endpoints and nonzero at the cut has a smooth compact test with zero total
pairing but unit pairing on the left piece. -/
theorem n04b_exists_balanced_compact_deriv_test {a b c : ℝ}
    (hc : c ∈ Ioo a b) {weight : ℝ → ℝ}
    (hweight : ContinuousOn weight (Icc a b)) (ha : weight a = 0) (hb : weight b = 0)
    (hcut : weight c ≠ 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo a b ∧
      (∫ x in a..b, weight x * deriv f x) = 0 ∧
      (∫ x in a..c, weight x * deriv f x) = 1 := by
  obtain ⟨f, hf, hfc, hfs, htotal, hhalf⟩ :=
    n04b_exists_zero_total_nonzero_half_test hc.1 hc.2 hweight ha hb hcut
  refine ⟨f, hf, hfc, hfs, ?_, ?_⟩
  · rw [← n04b_integral_weighted_deriv_eq_interval (hc.1.trans hc.2).le weight f hfs]
    exact htotal
  · simpa only [intervalIntegral.integral_of_le hc.1.le, integral_Ioc_eq_integral_Ioo]
      using hhalf

/-- Positivity on the component supplies the nonzero cut value in the
balanced-test construction. No differentiability assumption on the weight
is necessary. -/
theorem n04b_exists_balanced_compact_deriv_test_of_pos {a b c : ℝ}
    (hc : c ∈ Ioo a b) {weight : ℝ → ℝ}
    (hweight : ContinuousOn weight (Icc a b)) (ha : weight a = 0) (hb : weight b = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < weight x) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo a b ∧
      (∫ x in a..b, weight x * deriv f x) = 0 ∧
      (∫ x in a..c, weight x * deriv f x) ≠ 0 := by
  obtain ⟨f, hf, hfc, hfs, htotal, hhalf⟩ :=
    n04b_exists_balanced_compact_deriv_test hc hweight ha hb (hpos c hc).ne'
  exact ⟨f, hf, hfc, hfs, htotal, by rw [hhalf]; exact one_ne_zero⟩

end ContinuousFlexibility.Analysis
