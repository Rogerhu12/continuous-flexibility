import ContinuousFlexibility.Analysis.N06PositiveClippedJets
import ContinuousFlexibility.Analysis.N06PositiveReferenceHeightBounds

/-!
# Polynomial finite jets of the actual positive reference height

The logarithmic endpoint interpolation is built from the same fixed
cutoff as the coordinate. Its two jets have a polynomial bound. The
actual height stays bounded by the endpoint value bounds, so applying
the exponential chain rule introduces no uncontrolled exponential of
the derivative bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem N06ScalarJetTwoBound.exp
    {f : ℝ → ℝ} {x A B : ℝ} (hf : ContDiff ℝ ∞ f)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hfb : N06ScalarJetTwoBound f x B)
    (hvalue : Real.exp (f x) ≤ A) :
    N06ScalarJetTwoBound (fun t => Real.exp (f t)) x (2 * A * B ^ 2) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hAB : A * B ≤ A * B ^ 2 := mul_le_mul_of_nonneg_left hBB hA
  have hA2 : A ≤ A * B ^ 2 := le_mul_of_one_le_right hA hB2
  have hAB2 : 0 ≤ A * B ^ 2 := mul_nonneg hA (sq_nonneg B)
  constructor
  · rw [abs_of_pos (Real.exp_pos _)]
    exact hvalue.trans (by nlinarith)
  · have hd : deriv (fun t => Real.exp (f t)) x = Real.exp (f x) * deriv f x := by
      simpa only [Function.comp_def] using ((Real.hasDerivAt_exp (f x)).comp x
        (hf.differentiable (by simp) x).hasDerivAt).deriv
    rw [hd, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul hvalue hfb.first (abs_nonneg _) hA).trans (by nlinarith)
  · rw [n06_deriv_two_comp Real.contDiff_exp hf]
    simp only [Real.deriv_exp]
    have hfirst : |Real.exp (f x) * deriv f x ^ 2| ≤ A * B ^ 2 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
      exact mul_le_mul hvalue (pow_le_pow_left₀ (abs_nonneg _) hfb.first 2)
        (sq_nonneg _) hA
    have hsecond : |Real.exp (f x) * deriv (deriv f) x| ≤ A * B := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul hvalue hfb.second (abs_nonneg _) hA
    have he := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
    nlinarith

/-- Bounds for the actual endpoint heights and their logarithmic two
jets give a polynomial bound for the constructed height's two jets,
while its reciprocal has the original endpoint value bound. -/
theorem n06_positiveReferenceHeight_twoJet_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ l r δ B : ℝ, ∀ hL hR : ℝ → ℝ,
      0 < δ → 1 ≤ B → δ⁻¹ ≤ B → 2 * δ ≤ r - l →
      (∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ hL x) →
      (∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ hR x) →
      (∀ x ∈ Metric.ball l δ, 1 / B ≤ hL x ∧ hL x ≤ B) →
      (∀ x ∈ Metric.ball r δ, 1 / B ≤ hR x ∧ hR x ≤ B) →
      (∀ x ∈ Metric.ball l δ, N06ScalarJetTwoBound (fun t => Real.log (hL t)) x B) →
      (∀ x ∈ Metric.ball r δ, N06ScalarJetTwoBound (fun t => Real.log (hR t)) x B) →
      ∀ x, N06ScalarJetTwoBound (positiveReferenceHeight l r δ hL hR) x (C * B ^ 7) ∧
        1 / positiveReferenceHeight l r δ hL hR x ≤ B := by
  obtain ⟨Ccut, hCcut, hcut⟩ := n06_positiveEndpointCutoff_twoJet_bound
  have hCsq : 1 ≤ Ccut ^ 2 := one_le_pow₀ hCcut
  refine ⟨128 * Ccut ^ 2, by nlinarith, ?_⟩
  intro l r δ B hL hR hδ hB hδB hgap hLsm hRsm hbL hbR hjL hjR x
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hC0 : 0 ≤ Ccut := zero_le_one.trans hCcut
  have hpL : ∀ y ∈ Metric.ball l δ, 0 < hL y :=
    fun y hy => (one_div_pos.mpr hBp).trans_le (hbL y hy).1
  have hpR : ∀ y ∈ Metric.ball r δ, 0 < hR y :=
    fun y hy => (one_div_pos.mpr hBp).trans_le (hbR y hy).1
  have hlL : ∀ y ∈ Metric.ball l δ, ContDiffAt ℝ ∞ (fun t => Real.log (hL t)) y :=
    fun y hy => (hLsm y hy).log (hpL y hy).ne'
  have hlR : ∀ y ∈ Metric.ball r δ, ContDiffAt ℝ ∞ (fun t => Real.log (hR t)) y :=
    fun y hy => (hRsm y hy).log (hpR y hy).ne'
  have hleft := n06_positiveEndpointCutoff_mul_twoJet hδ hBp.le
    (mul_nonneg hC0 (sq_nonneg B)) hlL hjL
    (fun y => hcut l δ B y hδ hB hδB) x
  have hright := n06_positiveEndpointCutoff_mul_twoJet hδ hBp.le
    (mul_nonneg hC0 (sq_nonneg B)) hlR hjR
    (fun y => hcut r δ B y hδ hB hδB) x
  let f : ℝ → ℝ := fun t => positiveEndpointCutoff l δ t * Real.log (hL t) +
    positiveEndpointCutoff r δ t * Real.log (hR t)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_positiveEndpointCutoff_mul hδ hlL).add
      (contDiff_positiveEndpointCutoff_mul hδ hlR)
  have hfb : N06ScalarJetTwoBound f x (8 * Ccut * B ^ 3) := by
    convert hleft.add_at (contDiff_positiveEndpointCutoff_mul hδ hlL).contDiffAt
      (contDiff_positiveEndpointCutoff_mul hδ hlR).contDiffAt hright using 1 <;>
        first | rfl | ring
  have hB3 : 1 ≤ B ^ 3 := one_le_pow₀ hB
  have hCBB : 1 ≤ Ccut * B ^ 3 := one_le_mul_of_one_le_of_one_le hCcut hB3
  have hcoeff : 1 ≤ 8 * Ccut * B ^ 3 := by nlinarith
  have hheight := n06_positiveReferenceHeight_bounds hB hδ hgap hbL hbR x
  refine ⟨?_, hheight.2.2⟩
  have he : Real.exp (f x) ≤ B := hheight.2.1
  convert hfb.exp hf hBp.le hcoeff he using 1 <;> first | rfl | ring

end ContinuousFlexibility.Analysis
