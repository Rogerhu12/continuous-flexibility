import ContinuousFlexibility.Analysis.PositiveHeightTaylorInterpolation
import ContinuousFlexibility.Analysis.AngularTaylorPolynomial

/-!
# Value bounds for the actual logarithmic height interpolation

A collar small enough for the positive Taylor orders keeps each
logarithmic polynomial within one of its boundary value. Bounds for
the given height and its reciprocal therefore yield a polynomial
amplitude bound for the constructed height and its reciprocal.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveHeightTaylorInterpolation_one_germ
    (n : ℕ) {l r δ : ℝ} (hδ : 0 < δ) (h : Bool → PolarPoint → ℝ)
    (p : PolarPoint) (hL : p.1 ∉ Metric.ball l δ) (hR : p.1 ∉ Metric.ball r δ) :
    positiveHeightTaylorInterpolation n l r δ (fun _ => 1) h =ᶠ[𝓝 p]
      (fun _ => (1 : ℝ)) := by
  have hleft := (positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ hL).comp_tendsto
    (continuous_fst.continuousAt (x := p))
  have hright := (positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ hR).comp_tendsto
    (continuous_fst.continuousAt (x := p))
  filter_upwards [hleft, hright] with y hyL hyR
  have hyL' : positiveEndpointCutoff l δ y.1 = 0 := hyL
  have hyR' : positiveEndpointCutoff r δ y.1 = 0 := hyR
  simp only [positiveHeightTaylorInterpolation, endpointTaylorCorrection,
    hyL', hyR', zero_mul, zero_add, Real.exp_zero, one_mul]

theorem positiveHeightTaylorInterpolation_amplitude
    (n : ℕ) {l r δ M H : ℝ} {h : Bool → PolarPoint → ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hM : 0 ≤ M) (hH : 1 ≤ H)
    (hpositive : ∀ side θ, 0 < h side (if side then r else l, θ))
    (hupper : ∀ side θ, h side (if side then r else l, θ) ≤ H)
    (hinverse : ∀ side θ, (h side (if side then r else l, θ))⁻¹ ≤ H)
    (hlog : ∀ side j, 0 < j → j ≤ n → ∀ θ,
      |positiveHeightTaylorData l r (fun _ => 1) h side j θ| ≤ M)
    (hsmall : ((n + 1 : ℕ) : ℝ) * M * δ ≤ 1) (p : PolarPoint) :
    positiveHeightTaylorInterpolation n l r δ (fun _ => 1) h p ≤ Real.exp 2 * H ^ 2 ∧
      (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) h p)⁻¹ ≤ Real.exp 2 * H ^ 2 := by
  let A := positiveHeightTaylorData l r (fun _ => 1) h
  let e : Bool → ℝ := fun side => if side then r else l
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hA0 (side : Bool) : |A side 0 p.2| ≤ Real.log H := by
    have hu := Real.log_le_log (hpositive side p.2) (hupper side p.2)
    have hi := Real.log_le_log (inv_pos.mpr (hpositive side p.2)) (hinverse side p.2)
    rw [Real.log_inv] at hi
    change |Real.log (h side (e side, p.2) / 1)| ≤ Real.log H
    rw [div_one]
    exact abs_le.mpr ⟨by linarith, hu⟩
  have hterm (side : Bool) :
      |positiveEndpointCutoff (e side) δ p.1 *
        boundaryTaylorPolynomial n (e side) (A side) p| ≤ Real.log H + 1 := by
    apply abs_positiveEndpointCutoff_mul_le
      (f := fun x => boundaryTaylorPolynomial n (e side) (A side) (x, p.2))
      hδ (by linarith : 0 ≤ Real.log H + 1)
    intro x hx
    have hx' : |x - e side| ≤ δ := by
      exact (show |x - e side| < δ from (by
        simpa only [Metric.mem_ball, Real.dist_eq] using hx)).le
    have hd := (abs_boundaryTaylorPolynomial_sub_zero_le
      hδ.le hδone hM hx' (fun j hj hjn => hlog side j hj hjn p.2)).trans hsmall
    have ht := abs_add
      (boundaryTaylorPolynomial n (e side) (A side) (x, p.2) - A side 0 p.2) (A side 0 p.2)
    rw [sub_add_cancel] at ht
    linarith only [ht, hd, hA0 side]
  have hE : |endpointTaylorCorrection n l r δ A p| ≤ 2 * (Real.log H + 1) := by
    have hleft := hterm false
    have hright := hterm true
    change |positiveEndpointCutoff l δ p.1 * boundaryTaylorPolynomial n l (A false) p +
      positiveEndpointCutoff r δ p.1 * boundaryTaylorPolynomial n r (A true) p| ≤ _
    exact (abs_add _ _).trans (by
      change |positiveEndpointCutoff l δ p.1 * boundaryTaylorPolynomial n l (A false) p| +
        |positiveEndpointCutoff r δ p.1 * boundaryTaylorPolynomial n r (A true) p| ≤ _
      change |positiveEndpointCutoff l δ p.1 * boundaryTaylorPolynomial n l (A false) p| ≤ _ at hleft
      change |positiveEndpointCutoff r δ p.1 * boundaryTaylorPolynomial n r (A true) p| ≤ _ at hright
      linarith)
  have hexp : Real.exp (2 * (Real.log H + 1)) = Real.exp 2 * H ^ 2 := by
    rw [show 2 * (Real.log H + 1) = 2 + (Real.log H + Real.log H) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log hHpos]
    ring
  simp only [positiveHeightTaylorInterpolation, one_mul]
  change Real.exp (endpointTaylorCorrection n l r δ A p) ≤ _ ∧
    (Real.exp (endpointTaylorCorrection n l r δ A p))⁻¹ ≤ _
  constructor
  · exact (Real.exp_le_exp.mpr ((le_abs_self _).trans hE)).trans_eq hexp
  · rw [← Real.exp_neg]
    exact (Real.exp_le_exp.mpr ((neg_le_abs _).trans hE)).trans_eq hexp

end ContinuousFlexibility.Analysis
