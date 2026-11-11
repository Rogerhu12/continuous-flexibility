import ContinuousFlexibility.Analysis.N06PositiveClippedJets
import ContinuousFlexibility.Analysis.PositiveReferenceCoordinate

/-!
# Polynomial finite-jet bounds for the constructed positive coordinate

The two actual endpoint slopes, the reciprocal collar width and the
actual integral normalizer determine the first three coordinate jets.
No derivative bound for the constructed coordinate is supplied as an
input. The constant below comes only from the one fixed cutoff.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n06_positiveReferenceSlope_twoJet_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ l r δ B : ℝ, ∀ aL aR : ℝ → ℝ,
      0 < δ → 1 ≤ B → δ⁻¹ ≤ B →
      (∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x) →
      (∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x) →
      (∀ x ∈ Metric.ball l δ, N06ScalarJetTwoBound aL x B) →
      (∀ x ∈ Metric.ball r δ, N06ScalarJetTwoBound aR x B) →
      |positiveReferenceScale l r δ aL aR| ≤ B →
      ∀ x, N06ScalarJetTwoBound (positiveReferenceSlope l r δ aL aR) x (C * B ^ 3) := by
  obtain ⟨Ccut, hCcut, hcut⟩ := n06_positiveEndpointCutoff_twoJet_bound
  refine ⟨16 * Ccut, by linarith, ?_⟩
  intro l r δ B aL aR hδ hB hδB hL hR hbL hbR hscale x
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC0 : 0 ≤ Ccut := zero_le_one.trans hCcut
  let Q : ℝ := Ccut * B ^ 2
  have hQ : 0 ≤ Q := mul_nonneg hC0 (sq_nonneg B)
  have hcl := contDiff_positiveEndpointCutoff l δ
  have hcr := contDiff_positiveEndpointCutoff r δ
  have hl := contDiff_positiveEndpointCutoff_mul hδ hL
  have hr := contDiff_positiveEndpointCutoff_mul hδ hR
  have hbcl : N06ScalarJetTwoBound (positiveEndpointCutoff l δ) x Q :=
    hcut l δ B x hδ hB hδB
  have hbcr : N06ScalarJetTwoBound (positiveEndpointCutoff r δ) x Q :=
    hcut r δ B x hδ hB hδB
  have hbl : N06ScalarJetTwoBound
      (fun t => positiveEndpointCutoff l δ t * aL t) x (4 * Q * B) :=
    n06_positiveEndpointCutoff_mul_twoJet hδ hB0 hQ hL hbL
      (fun y => hcut l δ B y hδ hB hδB) x
  have hbr : N06ScalarJetTwoBound
      (fun t => positiveEndpointCutoff r δ t * aR t) x (4 * Q * B) :=
    n06_positiveEndpointCutoff_mul_twoJet hδ hB0 hQ hR hbR
      (fun y => hcut r δ B y hδ hB hδB) x
  have hbone : N06ScalarJetTwoBound (fun _ : ℝ => (1 : ℝ)) x 1 := by
    constructor <;> simp only [abs_one, deriv_const', deriv_const, abs_zero] <;> norm_num
  have hbmid : N06ScalarJetTwoBound (fun t =>
      1 - positiveEndpointCutoff l δ t - positiveEndpointCutoff r δ t) x (1 + Q + Q) :=
    (hbone.sub_at contDiffAt_const hcl.contDiffAt hbcl).sub_at
      (contDiff_const.sub hcl).contDiffAt hcr.contDiffAt hbcr
  have hbscale := hbmid.const_mul (positiveReferenceScale l r δ aL aR)
  have hbends := hbl.add_at hl.contDiffAt hr.contDiffAt hbr
  have hbtotal := hbends.add_at (hl.add hr).contDiffAt
    (contDiff_const.mul ((contDiff_const.sub hcl).sub hcr)).contDiffAt hbscale
  apply hbtotal.mono
  have hB13 : B ≤ B ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 3)
  have hbig : B ≤ Ccut * B ^ 3 :=
    hB13.trans (le_mul_of_one_le_left (pow_nonneg hB0 _) hCcut)
  have hweighted := mul_le_mul_of_nonneg_right hscale (by positivity : 0 ≤ 1 + Q + Q)
  dsimp only [Q] at hweighted ⊢
  nlinarith

/-- Integrating the actual slope retains its first two derivative bounds
as the second and third derivatives of the genuine global coordinate. -/
theorem n06_positiveReferenceCoordinate_threeJet_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ l r δ B : ℝ, ∀ aL aR : ℝ → ℝ,
      0 < δ → 1 ≤ B → δ⁻¹ ≤ B →
      (∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x) →
      (∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x) →
      (∀ x ∈ Metric.ball l δ, N06ScalarJetTwoBound aL x B) →
      (∀ x ∈ Metric.ball r δ, N06ScalarJetTwoBound aR x B) →
      |positiveReferenceScale l r δ aL aR| ≤ B →
      ∀ x, N06ScalarJetTwoBound (deriv (positiveReferenceCoordinate l r δ aL aR))
        x (C * B ^ 3) := by
  obtain ⟨C, hC, hbound⟩ := n06_positiveReferenceSlope_twoJet_bound
  refine ⟨C, hC, ?_⟩
  intro l r δ B aL aR hδ hB hδB hL hR hbL hbR hscale x
  have he : deriv (positiveReferenceCoordinate l r δ aL aR) =
      positiveReferenceSlope l r δ aL aR :=
    funext fun y => (hasDerivAt_positiveReferenceCoordinate hδ hL hR y).deriv
  rw [he]
  exact hbound l r δ B aL aR hδ hB hδB hL hR hbL hbR hscale x

end ContinuousFlexibility.Analysis
