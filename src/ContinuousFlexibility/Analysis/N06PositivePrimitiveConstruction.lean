import ContinuousFlexibility.Analysis.N06PositiveReferenceBounds
import ContinuousFlexibility.Analysis.N06PositiveReferenceSlopeJets
import ContinuousFlexibility.Analysis.N06PositiveReferenceHeightJets
import ContinuousFlexibility.Analysis.N06LogarithmicJets
import ContinuousFlexibility.Analysis.N06RadialInverseJets

/-!
# Quantitative construction with one explicit positive collar width

The raw endpoint values, reciprocal values and ordinary two-jets are
bounded by `A`. We choose the actual collar width `1 / (8 * A)` and
use the distinct jet cap `8 * A^4`. Thus the small-width condition and
the reciprocal-width bound are compatible. Logarithmic jets follow
from the ordinary height jets before the existing interpolation
estimates are applied.

The resulting maps are the original integral coordinate and logarithmic
height. All constants below depend only on the fixed cutoff; the endpoint
fields and the physical interval remain explicit inputs.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n06PositiveReferenceWidth (A : ℝ) : ℝ := 1 / (8 * A)

theorem n06_positiveReferenceWidth_bounds {A : ℝ} (hA : 1 ≤ A) :
    0 < n06PositiveReferenceWidth A ∧
      n06PositiveReferenceWidth A ≤ 1 / (4 * A) ∧
      (n06PositiveReferenceWidth A)⁻¹ ≤ 8 * A ^ 4 := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hA4 : A ≤ A ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hA (by norm_num : 1 ≤ 4)
  refine ⟨by unfold n06PositiveReferenceWidth; positivity, ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by positivity : 0 < 4 * A) (by linarith)
  · simp only [n06PositiveReferenceWidth, one_div, inv_inv]
    exact mul_le_mul_of_nonneg_left hA4 (by norm_num)

/-- Ordinary endpoint jets, reciprocal lower bounds and two-sided physical
length bounds produce uniform polynomial jets of the actual interpolation.
The hypotheses concern the chosen physical collars; no estimate for the
constructed coordinate, height or inverse is assumed. -/
theorem n06_positiveReference_forward_construction :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ l r A : ℝ, ∀ aL aR hL hR : ℝ → ℝ,
      1 ≤ A → (1 / A ≤ r - l ∧ r - l ≤ A) →
      (∀ x ∈ Metric.ball l (n06PositiveReferenceWidth A), ContDiffAt ℝ ∞ aL x) →
      (∀ x ∈ Metric.ball r (n06PositiveReferenceWidth A), ContDiffAt ℝ ∞ aR x) →
      (∀ x ∈ Metric.ball l (n06PositiveReferenceWidth A), ContDiffAt ℝ ∞ hL x) →
      (∀ x ∈ Metric.ball r (n06PositiveReferenceWidth A), ContDiffAt ℝ ∞ hR x) →
      (∀ x ∈ Metric.ball l (n06PositiveReferenceWidth A),
        1 / A ≤ aL x ∧ N06ScalarJetTwoBound aL x A) →
      (∀ x ∈ Metric.ball r (n06PositiveReferenceWidth A),
        1 / A ≤ aR x ∧ N06ScalarJetTwoBound aR x A) →
      (∀ x ∈ Metric.ball l (n06PositiveReferenceWidth A),
        1 / A ≤ hL x ∧ N06ScalarJetTwoBound hL x A) →
      (∀ x ∈ Metric.ball r (n06PositiveReferenceWidth A),
        1 / A ≤ hR x ∧ N06ScalarJetTwoBound hR x A) →
      (let δ : ℝ := n06PositiveReferenceWidth A
       let Y : ℝ → ℝ := positiveReferenceCoordinate l r δ aL aR
       let H : ℝ → ℝ := positiveReferenceHeight l r δ hL hR
       ContDiff ℝ ∞ Y ∧ Function.Bijective Y ∧
         ContDiff ℝ ∞ (Function.invFun Y) ∧ Y l = 0 ∧ Y r = 1 ∧
         ContDiff ℝ ∞ H ∧
         (∀ x, 1 / (2 * A) ≤ deriv Y x ∧ deriv Y x ≤ 2 * A) ∧
         (∀ x, 1 / A ≤ H x ∧ H x ≤ A ∧ 1 / H x ≤ A) ∧
         ∀ x, N06ScalarJetTwoBound H x (C0 * A ^ 28) ∧
           N06ScalarJetTwoBound (deriv Y) x (C0 * A ^ 28)) := by
  obtain ⟨Cs, hCs, hslope⟩ := n06_positiveReferenceCoordinate_threeJet_bound
  obtain ⟨Ch, hCh, hheight⟩ := n06_positiveReferenceHeight_twoJet_bound
  let C0 : ℝ := (Cs + Ch + 1) * 8 ^ 7
  have hC0 : 1 ≤ C0 :=
    one_le_mul_of_one_le_of_one_le (by linarith : 1 ≤ Cs + Ch + 1) (by norm_num)
  refine ⟨C0, hC0, ?_⟩
  intro l r A aL aR hL hR hA hwidth hsL hsR hhL hhR hbL hbR hkL hkR
  let δ : ℝ := n06PositiveReferenceWidth A
  let J : ℝ := 8 * A ^ 4
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hAi : 0 < 1 / A := one_div_pos.mpr hAp
  have hA4 : A ≤ A ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hA (by norm_num : 1 ≤ 4)
  have hA4one : 1 ≤ A ^ 4 := one_le_pow₀ hA
  have hAJ : A ≤ J := by dsimp only [J]; nlinarith
  have hJ : 1 ≤ J := hA.trans hAJ
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hlogJ : 2 * A ^ 4 ≤ J := by
    dsimp only [J]
    nlinarith [pow_nonneg hAp.le 4]
  have hscaleJ : 2 * A ≤ J := by dsimp only [J]; nlinarith
  obtain ⟨hδ, hδsmall, hδJ⟩ := n06_positiveReferenceWidth_bounds hA
  have hsLb : ∀ x ∈ Metric.ball l δ, 1 / A ≤ aL x ∧ aL x ≤ A :=
    fun x hx => ⟨(hbL x hx).1, (le_abs_self _).trans (hbL x hx).2.value⟩
  have hsRb : ∀ x ∈ Metric.ball r δ, 1 / A ≤ aR x ∧ aR x ≤ A :=
    fun x hx => ⟨(hbR x hx).1, (le_abs_self _).trans (hbR x hx).2.value⟩
  have hhLb : ∀ x ∈ Metric.ball l δ, 1 / A ≤ hL x ∧ hL x ≤ A :=
    fun x hx => ⟨(hkL x hx).1, (le_abs_self _).trans (hkL x hx).2.value⟩
  have hhRb : ∀ x ∈ Metric.ball r δ, 1 / A ≤ hR x ∧ hR x ≤ A :=
    fun x hx => ⟨(hkR x hx).1, (le_abs_self _).trans (hkR x hx).2.value⟩
  obtain ⟨hgap, _, _, _, _, hscaleL, hscaleU⟩ :=
    n06_positiveReferenceScale_bounds hA hwidth hδ hδsmall hsL hsR hsLb hsRb
  have hscale : |positiveReferenceScale l r δ aL aR| ≤ J := by
    rw [abs_of_pos ((one_div_pos.mpr (by positivity : 0 < 2 * A)).trans_le hscaleL)]
    exact hscaleU.trans hscaleJ
  have hlog (c : ℝ) (f : ℝ → ℝ)
      (hsm : ∀ x ∈ Metric.ball c δ, ContDiffAt ℝ ∞ f x)
      (hb : ∀ x ∈ Metric.ball c δ, 1 / A ≤ f x ∧ N06ScalarJetTwoBound f x A) :
      ∀ x ∈ Metric.ball c δ,
        N06ScalarJetTwoBound (fun t => Real.log (f t)) x J := by
    intro x hx
    have hfp : 0 < f x := hAi.trans_le (hb x hx).1
    have hfi : (f x)⁻¹ ≤ A := by
      have he := one_div_le_one_div_of_le hAi (hb x hx).1
      simpa only [one_div_one_div, one_div, inv_inv] using he
    exact ((hb x hx).2.log_at (hsm x hx) hA hfp hfi).mono hlogJ
  have hinvJA : 1 / J ≤ 1 / A := one_div_le_one_div_of_le hAp hAJ
  have hhLJ : ∀ x ∈ Metric.ball l δ, 1 / J ≤ hL x ∧ hL x ≤ J :=
    fun x hx => ⟨hinvJA.trans (hhLb x hx).1, (hhLb x hx).2.trans hAJ⟩
  have hhRJ : ∀ x ∈ Metric.ball r δ, 1 / J ≤ hR x ∧ hR x ≤ J :=
    fun x hx => ⟨hinvJA.trans (hhRb x hx).1, (hhRb x hx).2.trans hAJ⟩
  obtain ⟨hY, hbij, hRsmInv, hyL, hyR, hYbounds⟩ :=
    n06_positiveReferenceCoordinate_bounds hA hwidth hδ hδsmall hsL hsR hsLb hsRb
  have hH : ContDiff ℝ ∞ (positiveReferenceHeight l r δ hL hR) :=
    contDiff_positiveReferenceHeight hδ hhL hhR
      (fun x hx => hAi.trans_le (hhLb x hx).1)
      (fun x hx => hAi.trans_le (hhRb x hx).1)
  refine ⟨hY, hbij, hRsmInv, hyL, hyR, hH, hYbounds,
    (fun x => n06_positiveReferenceHeight_bounds hA hδ hgap.le hhLb hhRb x), ?_⟩
  intro x
  have hHb := (hheight l r δ J hL hR hδ hJ hδJ hgap.le hhL hhR hhLJ hhRJ
    (hlog l hL hhL hkL) (hlog r hR hhR hkR) x).1
  have hYb := hslope l r δ J aL aR hδ hJ hδJ hsL hsR
    (fun t ht => (hbL t ht).2.mono hAJ) (fun t ht => (hbR t ht).2.mono hAJ) hscale x
  have hpoly (c : ℝ) (hc : c ≤ Cs + Ch + 1) : c * J ^ 7 ≤ C0 * A ^ 28 := by
    calc
      _ ≤ (Cs + Ch + 1) * J ^ 7 := mul_le_mul_of_nonneg_right hc (pow_nonneg hJp.le _)
      _ = _ := by dsimp only [C0, J]; ring
  refine ⟨hHb.mono (hpoly Ch (by linarith)), hYb.mono ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hJ (by norm_num : 3 ≤ 7)) (zero_le_one.trans hCs)).trans
      (hpoly Cs (by linarith))

end ContinuousFlexibility.Analysis
