import ContinuousFlexibility.Analysis.PositiveReferenceCoordinate
import ContinuousFlexibility.Analysis.PositiveReferenceHeight

/-!
# Quantitative bounds for the actual positive reference interpolation

The middle normalizer is the integral normalizer of the existing
construction. Bounds for the actual endpoint slopes and the interval
length control this normalizer and the resulting coordinate slope,
including its reciprocal. The height estimate uses the actual
logarithmic interpolation and does not replace it by a proposed gauge.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n06_positiveReferenceEndMass_nonneg
    {l r δ : ℝ} {aL aR : ℝ → ℝ} (hlr : l ≤ r) (hδ : 0 < δ)
    (hL : ∀ x ∈ Metric.ball l δ, 0 ≤ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, 0 ≤ aR x) :
    0 ≤ positiveReferenceEndMass l r δ aL aR := by
  apply intervalIntegral.integral_nonneg hlr
  intro x _
  have hleft := positiveEndpointCutoff_mul_lower hδ hL x
  have hright := positiveEndpointCutoff_mul_lower hδ hR x
  simp only [zero_mul] at hleft hright
  exact add_nonneg hleft hright

theorem n06_positiveReferenceMiddleMass_le
    {l r δ : ℝ} (hlr : l ≤ r) :
    positiveReferenceMiddleMass l r δ ≤ r - l := by
  have hc : Continuous (fun x : ℝ =>
      1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x) :=
    (continuous_const.sub (contDiff_positiveEndpointCutoff l δ).continuous).sub
      (contDiff_positiveEndpointCutoff r δ).continuous
  have hi := intervalIntegral.integral_mono_on hlr
    (hc.intervalIntegrable (μ := volume) l r)
    (intervalIntegrable_const (c := (1 : ℝ)))
    (fun x _ => by
      have hL := positiveEndpointCutoff_nonneg l δ x
      have hR := positiveEndpointCutoff_nonneg r δ x
      linarith)
  simpa only [positiveReferenceMiddleMass, intervalIntegral.integral_const,
    smul_eq_mul, mul_one] using hi

/-- A collar of width at most `1/(4B)` leaves at least half the middle
mass and spends at most half the total coordinate increment at the ends.
The upper and lower bounds concern the actual integral normalizer. -/
theorem n06_positiveReferenceScale_bounds
    {l r δ B : ℝ} {aL aR : ℝ → ℝ} (hB : 1 ≤ B)
    (hwidth : 1 / B ≤ r - l ∧ r - l ≤ B)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / (4 * B))
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x)
    (hbL : ∀ x ∈ Metric.ball l δ, 1 / B ≤ aL x ∧ aL x ≤ B)
    (hbR : ∀ x ∈ Metric.ball r δ, 1 / B ≤ aR x ∧ aR x ≤ B) :
    2 * δ < r - l ∧
      0 ≤ positiveReferenceEndMass l r δ aL aR ∧
      positiveReferenceEndMass l r δ aL aR ≤ 1 / 2 ∧
      1 / (2 * B) ≤ positiveReferenceMiddleMass l r δ ∧
      positiveReferenceMiddleMass l r δ ≤ B ∧
      1 / (2 * B) ≤ positiveReferenceScale l r δ aL aR ∧
      positiveReferenceScale l r δ aL aR ≤ 2 * B := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBinv : 0 < 1 / B := one_div_pos.mpr hBp
  have hwidthB : 1 ≤ (r - l) * B := (div_le_iff₀ hBp).mp hwidth.1
  have hδB : δ * (4 * B) ≤ 1 := (le_div_iff₀ (by positivity)).mp hδsmall
  have hlr : l < r := by linarith [hwidth.1]
  have hgap : 2 * δ < r - l := by nlinarith
  have he0 := n06_positiveReferenceEndMass_nonneg hlr.le hδ
    (fun x hx => hBinv.le.trans (hbL x hx).1)
    (fun x hx => hBinv.le.trans (hbR x hx).1)
  have he1 : positiveReferenceEndMass l r δ aL aR ≤ 1 / 2 := by
    apply (positiveReferenceEndMass_le hδ hBp.le hL hR
      (fun x hx => by rw [abs_of_pos (hBinv.trans_le (hbL x hx).1)]; exact (hbL x hx).2)
      (fun x hx => by rw [abs_of_pos (hBinv.trans_le (hbR x hx).1)]; exact (hbR x hx).2)).trans
    nlinarith
  have hm0 : 1 / (2 * B) ≤ positiveReferenceMiddleMass l r δ := by
    have hm := integral_positiveEndpointCutoff_complement_lower (l := l) (r := r) hδ
    change r - l - 2 * δ ≤ positiveReferenceMiddleMass l r δ at hm
    have hmB := mul_le_mul_of_nonneg_right hm hBp.le
    apply (div_le_iff₀ (by positivity : 0 < 2 * B)).mpr
    nlinarith
  have hm1 : positiveReferenceMiddleMass l r δ ≤ B :=
    (n06_positiveReferenceMiddleMass_le hlr.le).trans hwidth.2
  have hmp : 0 < positiveReferenceMiddleMass l r δ :=
    (one_div_pos.mpr (by positivity : 0 < 2 * B)).trans_le hm0
  have hn : 0 ≤ 1 - positiveReferenceEndMass l r δ aL aR := by linarith
  have hscale0 : 1 / (2 * B) ≤ positiveReferenceScale l r δ aL aR := by
    change 1 / (2 * B) ≤ (1 - positiveReferenceEndMass l r δ aL aR) /
      positiveReferenceMiddleMass l r δ
    calc
      _ = (1 / 2 : ℝ) / B := by ring
      _ ≤ (1 - positiveReferenceEndMass l r δ aL aR) / B :=
        div_le_div_of_nonneg_right (by linarith) hBp.le
      _ ≤ _ := div_le_div_of_nonneg_left hn hmp hm1
  have hscale1 : positiveReferenceScale l r δ aL aR ≤ 2 * B := by
    change (1 - positiveReferenceEndMass l r δ aL aR) /
      positiveReferenceMiddleMass l r δ ≤ 2 * B
    apply (div_le_iff₀ hmp).mpr
    have hmB : 1 ≤ positiveReferenceMiddleMass l r δ * (2 * B) :=
      (div_le_iff₀ (by positivity : 0 < 2 * B)).mp hm0
    nlinarith
  exact ⟨hgap, he0, he1, hm0, hm1, hscale0, hscale1⟩

/-- The actual global coordinate has uniform two-sided slope bounds,
not merely a qualitative positive minimum chosen after construction. -/
theorem n06_positiveReferenceCoordinate_bounds
    {l r δ B : ℝ} {aL aR : ℝ → ℝ} (hB : 1 ≤ B)
    (hwidth : 1 / B ≤ r - l ∧ r - l ≤ B)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / (4 * B))
    (hL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ aL x)
    (hR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ aR x)
    (hbL : ∀ x ∈ Metric.ball l δ, 1 / B ≤ aL x ∧ aL x ≤ B)
    (hbR : ∀ x ∈ Metric.ball r δ, 1 / B ≤ aR x ∧ aR x ≤ B) :
    let Y := positiveReferenceCoordinate l r δ aL aR
    ContDiff ℝ ∞ Y ∧ Function.Bijective Y ∧
      ContDiff ℝ ∞ (Function.invFun Y) ∧ Y l = 0 ∧ Y r = 1 ∧
      ∀ x, 1 / (2 * B) ≤ deriv Y x ∧ deriv Y x ≤ 2 * B := by
  obtain ⟨hgap, _, he, _, _, hscaleL, hscaleU⟩ :=
    n06_positiveReferenceScale_bounds hB hwidth hδ hδsmall hL hR hbL hbR
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hhalf : 1 / (2 * B) ≤ 1 / B := by
    apply one_div_le_one_div_of_le hBp
    linarith
  have hbij := positiveReferenceCoordinate_bijective_smoothInverse hδ hgap hL hR
    (one_div_pos.mpr hBp) (fun x hx => (hbL x hx).1)
    (fun x hx => (hbR x hx).1) (by linarith)
  refine ⟨contDiff_positiveReferenceCoordinate hδ hL hR, hbij.1, hbij.2,
    positiveReferenceCoordinate_left l r δ aL aR,
    positiveReferenceCoordinate_right hδ hgap hL hR, ?_⟩
  intro x
  rw [(hasDerivAt_positiveReferenceCoordinate hδ hL hR x).deriv]
  constructor
  · apply le_trans _ (positiveReferenceSlope_lower hδ hgap.le
      (fun y hy => (hbL y hy).1) (fun y hy => (hbR y hy).1) x)
    exact le_min hhalf hscaleL
  · have hηL := positiveEndpointCutoff_nonneg l δ x
    have hηR := positiveEndpointCutoff_nonneg r δ x
    have hη := positiveEndpointCutoff_add_le_one hδ hgap.le x
    have hmid : 0 ≤ 1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x := by
      linarith
    have hleft : positiveEndpointCutoff l δ x * aL x ≤
        2 * B * positiveEndpointCutoff l δ x := by
      by_cases hx : x ∈ Metric.ball l δ
      · nlinarith [(hbL x hx).2]
      · rw [positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hx, zero_mul, mul_zero]
    have hright : positiveEndpointCutoff r δ x * aR x ≤
        2 * B * positiveEndpointCutoff r δ x := by
      by_cases hx : x ∈ Metric.ball r δ
      · nlinarith [(hbR x hx).2]
      · rw [positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hx, zero_mul, mul_zero]
    have hmiddle := mul_le_mul_of_nonneg_right hscaleU hmid
    dsimp only [positiveReferenceSlope]
    nlinarith

end ContinuousFlexibility.Analysis
