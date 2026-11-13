import ContinuousFlexibility.Analysis.PositiveChartRangeGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Physical lower bounds for the same radial reference chart

The endpoint product in canonical coordinates is controlled by the
physical endpoint distance using the derivative of the actual chosen Y.
The resulting angular coefficient estimate uses the actual height H,
the physical profile coefficient, and the same derivative bound. None
of these hypotheses is a bound on a final canonical coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem PositiveChartRangeGeometry.cylinder_endpoint_values
    {Y H : ℝ → ℝ} {l u : ℝ} (hlu : l < u)
    (hG : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l u 0 1) :
    Y l = 0 ∧ Y u = 1 := by
  have hY : ContDiff ℝ ∞ Y := by
    simpa only [positiveReferenceCylinderChart, Function.comp_def, id_eq] using
      hG.chart_smooth.fst.comp (contDiff_id.prodMk (contDiff_const :
        ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))))
  have hYpos (r : ℝ) : 0 < deriv Y r := by
    have h := hG.jacobian_positive (r, 0)
    rw [planeJacobian_positiveReferenceCylinderChart (p := (r, 0))
      (hY.differentiable (by simp) r)] at h
    exact h
  have hmono := (strictMono_of_deriv_pos hYpos).monotone
  have hends (side : Bool) : Y (if side then u else l) = (if side then 1 else 0) := by
    have hp : (if side then u else l) ∈ Icc l u := by
      cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc]
      · exact ⟨le_rfl, hlu.le⟩
      · exact ⟨hlu.le, le_rfl⟩
    have hq : (if side then (1 : ℝ) else 0) ∈ Icc (0 : ℝ) 1 := by
      cases side <;> norm_num
    have hF : Y (if side then u else l) ∈ Icc (0 : ℝ) 1 :=
      (hG.maps_closed (show ((if side then u else l), (0 : ℝ)) ∈
        Icc l u ×ˢ (univ : Set ℝ) from ⟨hp, mem_univ _⟩)).1
    have hI : Function.invFun Y (if side then (1 : ℝ) else 0) ∈ Icc l u :=
      (hG.inverse_maps_closed (show ((if side then (1 : ℝ) else 0), (0 : ℝ)) ∈
        Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) from ⟨hq, mem_univ _⟩)).1
    have hright : Y (Function.invFun Y (if side then 1 else 0)) =
        (if side then 1 else 0) :=
      congrArg Prod.fst (hG.right_inverse ((if side then 1 else 0), 0))
    cases side
    · exact le_antisymm ((hmono hI.1).trans_eq hright) hF.1
    · exact le_antisymm hF.2 (hright.symm.trans_le (hmono hI.2))
  exact ⟨hends false, hends true⟩

theorem radial_reference_endpoint_product_le
    {Y : ℝ → ℝ} {l u M r : ℝ}
    (hY : ContinuousOn Y (Icc l u))
    (hYd : DifferentiableOn ℝ Y (Ioo l u))
    (hupper : ∀ x ∈ Ioo l u, deriv Y x ≤ M)
    (hleft : Y l = 0) (hright : Y u = 1) (hr : r ∈ Ioo l u) :
    Y r * (1 - Y r) ≤ M * min (r - l) (u - r) := by
  have hdiff : DifferentiableOn ℝ Y (interior (Icc l u)) := by
    simpa only [interior_Icc] using hYd
  have hbound : ∀ x ∈ interior (Icc l u), deriv Y x ≤ M := by
    simpa only [interior_Icc] using hupper
  have hinc := (convex_Icc l u).image_sub_le_mul_sub_of_deriv_le hY hdiff hbound
  have hl : Y r ≤ M * (r - l) := by
    simpa only [hleft, sub_zero] using
      hinc l ⟨le_rfl, hr.1.le.trans hr.2.le⟩ r ⟨hr.1.le, hr.2.le⟩ hr.1.le
  have hu : 1 - Y r ≤ M * (u - r) := by
    simpa only [hright] using
      hinc r ⟨hr.1.le, hr.2.le⟩ u ⟨hr.1.le.trans hr.2.le, le_rfl⟩ hr.2.le
  have hprodL : Y r * (1 - Y r) ≤ M * (r - l) :=
    (by nlinarith only [sq_nonneg (Y r)] : Y r * (1 - Y r) ≤ Y r).trans hl
  have hprodR : Y r * (1 - Y r) ≤ M * (u - r) :=
    (by nlinarith only [sq_nonneg (1 - Y r)] :
      Y r * (1 - Y r) ≤ 1 - Y r).trans hu
  rcases le_total (r - l) (u - r) with h | h
  · simpa only [min_eq_left h] using hprodL
  · simpa only [min_eq_right h] using hprodR

theorem radial_reference_c_lower_of_physical_profile
    {Y H f : ℝ → ℝ} {l u M h k r : ℝ}
    (hY : ContinuousOn Y (Icc l u))
    (hYd : DifferentiableOn ℝ Y (Ioo l u))
    (hupper : ∀ x ∈ Ioo l u, deriv Y x ≤ M)
    (hleft : Y l = 0) (hright : Y u = 1) (hr : r ∈ Ioo l u)
    (hYr : Y r ∈ Icc (0 : ℝ) 1) (hM : 0 < M)
    (hh : 0 ≤ h) (hH : h ≤ H r) (hk : 0 ≤ k)
    (hYpos : 0 < deriv Y r)
    (hprofile : k * min (r - l) (u - r) ≤ f r) :
    (h ^ 2 * k / M ^ 2) * (Y r * (1 - Y r)) ≤
      H r ^ 2 / deriv Y r * f r := by
  let t := Y r * (1 - Y r)
  have ht : 0 ≤ t := mul_nonneg hYr.1 (sub_nonneg.mpr hYr.2)
  have htM : t / M ≤ min (r - l) (u - r) := by
    apply (div_le_iff₀ hM).2
    simpa only [mul_comm] using
      radial_reference_endpoint_product_le hY hYd hupper hleft hright hr
  have hf : k * (t / M) ≤ f r :=
    (mul_le_mul_of_nonneg_left htM hk).trans hprofile
  have hfactor : h ^ 2 / M ≤ H r ^ 2 / deriv Y r :=
    (div_le_div_of_nonneg_left (sq_nonneg h) hYpos (hupper r hr)).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hh hH 2) hYpos.le)
  calc
    (h ^ 2 * k / M ^ 2) * (Y r * (1 - Y r)) =
        (h ^ 2 / M) * (k * (t / M)) := by
      dsimp only [t]
      field_simp [hM.ne']
      <;> ring
    _ ≤ H r ^ 2 / deriv Y r * f r :=
      mul_le_mul hfactor hf (mul_nonneg hk (div_nonneg ht hM.le))
        (div_nonneg (sq_nonneg _) hYpos.le)

end ContinuousFlexibility.Analysis
