module

public import ContinuousFlexibility.Analysis.PositiveReferenceIdentity
public import ContinuousFlexibility.Analysis.PositiveReferenceHeight

/-!
# Numerical bounds for the same reference coordinate and height

The normalizing scale is controlled by the actual endpoint integral
and middle cutoff mass. The derivative bound is a convex combination
bound. The logarithmic height construction preserves polynomial value
and reciprocal bounds, without exponentiating a polynomial jet bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem positiveReferenceScale_two_sided
    {l r δ A M : ℝ} {a : Bool → ℝ → ℝ}
    (hδ : 0 < δ) (hgap : 4 * δ ≤ r - l) (hA : 0 < A) (hM : 0 ≤ M)
    (hsmooth : ∀ (side : Bool) (x : ℝ), x ∈ Metric.ball (if side then r else l) δ →
      ContDiffAt ℝ ∞ (a side) x)
    (hlower : ∀ (side : Bool) (x : ℝ), x ∈ Metric.ball (if side then r else l) δ → A ≤ a side x)
    (hupper : ∀ (side : Bool) (x : ℝ), x ∈ Metric.ball (if side then r else l) δ → |a side x| ≤ M)
    (hmass : 2 * M * δ ≤ 1 / 2) :
    1 / (2 * (r - l)) ≤ positiveReferenceScale l r δ (a false) (a true) ∧
      positiveReferenceScale l r δ (a false) (a true) ≤ 2 / (r - l) := by
  have hspan : 0 < r - l := by linarith only [hδ, hgap]
  have hsep : 2 * δ < r - l := by linarith only [hδ, hgap]
  have hmidpos : 0 < positiveReferenceMiddleMass l r δ :=
    integral_positiveEndpointCutoff_complement_pos hδ hsep
  have hmidupper := positiveReferenceMiddleMass_le_width hδ hsep
  have hmidlower : (r - l) / 2 ≤ positiveReferenceMiddleMass l r δ := by
    have h := integral_positiveEndpointCutoff_complement_lower (l := l) (r := r) hδ
    change r - l - 2 * δ ≤ positiveReferenceMiddleMass l r δ at h
    linarith only [h, hgap]
  have hendupper : positiveReferenceEndMass l r δ (a false) (a true) ≤ 1 / 2 :=
    (positiveReferenceEndMass_le hδ hM (hsmooth false) (hsmooth true)
      (hupper false) (hupper true)).trans hmass
  have hendnonneg : 0 ≤ positiveReferenceEndMass l r δ (a false) (a true) := by
    apply intervalIntegral.integral_nonneg (show l ≤ r by linarith only [hspan])
    intro x _
    have hL := positiveEndpointCutoff_mul_lower hδ (hlower false) x
    have hR := positiveEndpointCutoff_mul_lower hδ (hlower true) x
    have hnL := positiveEndpointCutoff_nonneg l δ x
    have hnR := positiveEndpointCutoff_nonneg r δ x
    have hpL : 0 ≤ A * positiveEndpointCutoff l δ x := mul_nonneg hA.le hnL
    have hpR : 0 ≤ A * positiveEndpointCutoff r δ x := mul_nonneg hA.le hnR
    exact add_nonneg (hpL.trans hL) (hpR.trans hR)
  constructor
  · calc
      _ = (1 / 2 : ℝ) / (r - l) := by field_simp [hspan.ne'] <;> ring
      _ ≤ (1 / 2 : ℝ) / positiveReferenceMiddleMass l r δ :=
        div_le_div_of_nonneg_left (by norm_num) hmidpos hmidupper
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hendupper]) hmidpos.le
  · calc
      _ ≤ 1 / positiveReferenceMiddleMass l r δ :=
        div_le_div_of_nonneg_right (by linarith only [hendnonneg]) hmidpos.le
      _ ≤ 1 / ((r - l) / 2) :=
        div_le_div_of_nonneg_left zero_le_one (half_pos hspan) hmidlower
      _ = _ := by field_simp [hspan.ne'] <;> ring

theorem positiveReferenceCoordinate_deriv_bounds
    {l r δ A M : ℝ} {a : Bool → ℝ → ℝ}
    (hδ : 0 < δ) (hgap : 4 * δ ≤ r - l) (hA : 0 < A) (hM : 0 ≤ M)
    (hsmooth : ∀ (side : Bool) (x : ℝ), x ∈ Metric.ball (if side then r else l) δ →
      ContDiffAt ℝ ∞ (a side) x)
    (hlower : ∀ (side : Bool) (x : ℝ), x ∈ Metric.ball (if side then r else l) δ → A ≤ a side x)
    (hupper : ∀ (side : Bool) (x : ℝ), x ∈ Metric.ball (if side then r else l) δ → |a side x| ≤ M)
    (hmass : 2 * M * δ ≤ 1 / 2) (x : ℝ) :
    min A (1 / (2 * (r - l))) ≤
        deriv (positiveReferenceCoordinate l r δ (a false) (a true)) x ∧
      deriv (positiveReferenceCoordinate l r δ (a false) (a true)) x ≤
        max M (2 / (r - l)) := by
  have hscale := positiveReferenceScale_two_sided hδ hgap hA hM hsmooth hlower hupper hmass
  have hsep : 2 * δ ≤ r - l := by linarith only [hδ, hgap]
  rw [(hasDerivAt_positiveReferenceCoordinate (l := l) (r := r) hδ (hsmooth false) (hsmooth true) x).deriv]
  constructor
  · exact (min_le_min le_rfl hscale.1).trans
      (positiveReferenceSlope_lower hδ hsep (hlower false) (hlower true) x)
  · let K : ℝ := max M (2 / (r - l))
    have hclip (side : Bool) :
        positiveEndpointCutoff (if side then r else l) δ x * a side x ≤
          K * positiveEndpointCutoff (if side then r else l) δ x := by
      by_cases hx : x ∈ Metric.ball (if side then r else l) δ
      · have hb : a side x ≤ K :=
          (le_abs_self _).trans ((hupper side x hx).trans (le_max_left _ _))
        simpa only [mul_comm K] using mul_le_mul_of_nonneg_left hb
          (positiveEndpointCutoff_nonneg _ δ x)
      · simp only [positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hx,
          zero_mul, mul_zero, le_refl]
    have hmid : 0 ≤ 1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x := by
      have h := positiveEndpointCutoff_add_le_one hδ hsep x
      linarith only [h]
    have hμ : positiveReferenceScale l r δ (a false) (a true) ≤ K :=
      hscale.2.trans (le_max_right _ _)
    have hm := mul_le_mul_of_nonneg_right hμ hmid
    have hL := hclip false
    have hR := hclip true
    change positiveEndpointCutoff l δ x * a false x ≤ K * positiveEndpointCutoff l δ x at hL
    change positiveEndpointCutoff r δ x * a true x ≤ K * positiveEndpointCutoff r δ x at hR
    change positiveEndpointCutoff l δ x * a false x +
      positiveEndpointCutoff r δ x * a true x +
      positiveReferenceScale l r δ (a false) (a true) *
        (1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x) ≤ K
    nlinarith only [hL, hR, hm]

/-- Bounds for the actual endpoint heights and their reciprocals on
the prescribed collars give a squared bound for the actual interpolation. -/
theorem positiveReferenceHeight_value_bounds
    {l r δ U : ℝ} {h : Bool → ℝ → ℝ} (hδ : 0 < δ) (hU : 1 ≤ U)
    (hpositive : ∀ (side : Bool) (x : ℝ), x ∈ Metric.ball (if side then r else l) δ → 0 < h side x)
    (hupper : ∀ (side : Bool) (x : ℝ), x ∈ Metric.ball (if side then r else l) δ → h side x ≤ U)
    (hinverse : ∀ (side : Bool) (x : ℝ), x ∈ Metric.ball (if side then r else l) δ → (h side x)⁻¹ ≤ U)
    (x : ℝ) :
    positiveReferenceHeight l r δ (h false) (h true) x ≤ U ^ 2 ∧
      (positiveReferenceHeight l r δ (h false) (h true) x)⁻¹ ≤ U ^ 2 := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  have hterm (side : Bool) :
      |positiveEndpointCutoff (if side then r else l) δ x * Real.log (h side x)| ≤
        Real.log U := by
    apply abs_positiveEndpointCutoff_mul_le hδ hlogU
    intro y hy
    have hu := Real.log_le_log (hpositive side y hy) (hupper side y hy)
    have hi := Real.log_le_log (inv_pos.mpr (hpositive side y hy)) (hinverse side y hy)
    rw [Real.log_inv] at hi
    exact abs_le.mpr ⟨by linarith only [hi], hu⟩
  let e : ℝ := positiveEndpointCutoff l δ x * Real.log (h false x) +
    positiveEndpointCutoff r δ x * Real.log (h true x)
  have he : |e| ≤ 2 * Real.log U := by
    have h := (abs_add_le _ _).trans (add_le_add (hterm false) (hterm true))
    simpa only [e, two_mul, Bool.false_eq_true, ite_false, ite_true] using h
  have hexp : Real.exp (2 * Real.log U) = U ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hUpos]
    ring
  change Real.exp e ≤ U ^ 2 ∧ (Real.exp e)⁻¹ ≤ U ^ 2
  constructor
  · exact (Real.exp_le_exp.mpr ((le_abs_self e).trans he)).trans_eq hexp
  · rw [← Real.exp_neg]
    exact (Real.exp_le_exp.mpr ((neg_le_abs e).trans he)).trans_eq hexp

end ContinuousFlexibility.Analysis
