module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Reciprocal resistance at a vanishing endpoint

A positive C¹ coefficient which vanishes at an endpoint is at most linear in
the distance to that endpoint. Its reciprocal therefore dominates the
nonintegrable inverse-distance kernel. The statement is independent of the
radial cell decomposition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem exists_endpoint_linear_bound {a b : ℝ} (hab : a < b)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (hwb : w b = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ r ∈ Icc a b, |w r| ≤ K * (b - r) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (hw.continuous_deriv le_rfl).norm.continuousOn
  let K : ℝ := |M| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound (r : ℝ) (hr : r ∈ Icc a b) : ‖deriv w r‖ ≤ K :=
    (hM ⟨r, hr, rfl⟩).trans (by dsimp [K]; linarith [le_abs_self M])
  refine ⟨K, hK, fun r hr => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ Icc a b) => hw.differentiable (by simp) x)
    hbound (convex_Icc a b) (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩) hr
  simpa only [hwb, sub_zero, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hr.2),
    neg_sub] using h

theorem not_integrableOn_inverse_of_vanishing_endpoint {a b : ℝ} (hab : a < b)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w)
    (hwpos : ∀ r ∈ Ioo a b, 0 < w r) (hwb : w b = 0) :
    ¬IntegrableOn (fun r => (w r)⁻¹) (Ioo a b) volume := by
  intro hi
  obtain ⟨K, _hK, hbound⟩ := exists_endpoint_linear_bound hab hw hwb
  have hmajor : IntegrableOn (fun r => K * (w r)⁻¹) (Ioo a b) volume := hi.const_mul K
  have hsmall : IntegrableOn (fun r => (r - b)⁻¹) (Ioo a b) volume := by
    apply hmajor.mono' ((measurable_id.sub_const b).inv.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hwr : 0 < w r := hwpos r hr
    have hbr : 0 < b - r := sub_pos.mpr hr.2
    have hwbnd : w r ≤ K * (b - r) := by
      simpa only [abs_of_pos hwr] using hbound r ⟨hr.1.le, hr.2.le⟩
    change ‖(r - b)⁻¹‖ ≤ K * (w r)⁻¹
    rw [Real.norm_eq_abs, abs_inv, abs_of_neg (sub_neg.mpr hr.2), neg_sub,
      ← div_eq_mul_inv]
    apply (le_div_iff₀ hwr).mpr
    have hh : w r / (b - r) ≤ K := (div_le_iff₀ hbr).mpr hwbnd
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hinterval : IntervalIntegrable (fun r => (r - b)⁻¹) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hsmall
  rcases intervalIntegrable_sub_inv_iff.mp hinterval with heq | hnot
  · exact hab.ne heq
  · exact hnot (by simp only [uIcc_of_le hab.le, mem_Icc]; exact ⟨hab.le, le_rfl⟩)

end ContinuousFlexibility.Analysis
