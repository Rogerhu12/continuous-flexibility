module

public import ContinuousFlexibility.Analysis.OpticalTravelVariation
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A quantitative interior optical collar from travel and a derivative bound

The travel integral forces a point with speed at least the mean speed.
A bound on the derivative of the squared speed then supplies an explicit
interior collar on which the speed remains bounded below. The width is
expressed in the travel lower bound, component length, and derivative
bound, so polynomial coefficient bounds can be substituted directly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff Interval

set_option backward.isDefEq.respectTransparency false

/-- A positive lower travel bound and an upper bound on the derivative
of the squared optical speed produce an explicit interior collar. -/
theorem exists_opticalSpeed_quantitative_collar
    {w : ℝ → ℝ} {l h τ M : ℝ} (hl : 0 < l) (hlh : l < h)
    (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hrootl : deriv w l = 0) (hrooth : deriv w h = 0)
    (hM : 0 ≤ M)
    (hbound : ∀ r ∈ Icc l h,
      |deriv (fun s => -deriv w s / (s * w s)) r| ≤ M)
    (hτ : 0 < τ) (htravel : τ ≤ opticalTravel w l h) :
    ∃ x : ℝ, let δ := (τ / (h - l)) ^ 2 / (4 * (M + 1))
      0 < δ ∧ l < x - δ ∧ x + δ < h ∧
      ∀ r ∈ Icc (x - δ) (x + δ), τ / (2 * (h - l)) ≤ opticalSpeed w r := by
  let Q (r : ℝ) := -deriv w r / (r * w r)
  have hd := (contDiff_infty_iff_deriv.mp hw).2
  have hQcont : ContinuousOn Q (Icc l h) :=
    hd.continuous.neg.continuousOn.div (continuous_id.mul hw.continuous).continuousOn
      (fun r hr => (mul_pos (hl.trans_le hr.1) (hpos r hr)).ne')
  have hvcont : ContinuousOn (opticalSpeed w) (Icc l h) :=
    Real.continuous_sqrt.comp_continuousOn hQcont
  obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hlh.le) hvcont
  have hlength : 0 < h - l := sub_pos.mpr hlh
  have hint : |opticalTravel w l h| ≤ opticalSpeed w x * (h - l) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := l) (b := h) (f := opticalSpeed w) (C := opticalSpeed w x) (fun r hr => by
        rw [uIoc_of_le hlh.le] at hr
        have hm := hxmax (show r ∈ Icc l h from ⟨hr.1.le, hr.2⟩)
        rw [Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ opticalSpeed w r from Real.sqrt_nonneg _)]
        exact hm)
    simpa only [opticalTravel, Real.norm_eq_abs, abs_of_pos hlength] using hb
  let s := τ / (h - l)
  have hs : 0 < s := div_pos hτ hlength
  have hsmax : s ≤ opticalSpeed w x := by
    apply (div_le_iff₀ hlength).mpr
    exact htravel.trans ((le_abs_self _).trans hint)
  have hQx : 0 < Q x := Real.sqrt_pos.mp (hs.trans_le hsmax)
  let q := s ^ 2
  have hq : 0 < q := pow_pos hs 2
  have hqmax : q ≤ Q x := by
    have hsq : opticalSpeed w x ^ 2 = Q x := Real.sq_sqrt hQx.le
    dsimp only [q]
    nlinarith [Real.sqrt_nonneg (Q x)]
  have hQdiff (r : ℝ) (hr : r ∈ Icc l h) : DifferentiableAt ℝ Q r :=
    (hd.differentiable (by simp) r).neg.div
      (differentiableAt_id.mul (hw.differentiable (by simp) r))
      (mul_pos (hl.trans_le hr.1) (hpos r hr)).ne'
  have hQlip (r : ℝ) (hr : r ∈ Icc l h) (t : ℝ) (ht : t ∈ Icc l h) :
      |Q t - Q r| ≤ M * |t - r| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc l h).norm_image_sub_le_of_norm_deriv_le hQdiff
        (fun u hu => by simpa only [Real.norm_eq_abs] using hbound u hu) hr ht
  have hQl : Q l = 0 := by simp only [Q, hrootl, neg_zero, zero_div]
  have hQh : Q h = 0 := by simp only [Q, hrooth, neg_zero, zero_div]
  have hleft : Q x ≤ M * (x - l) := by
    have hb := hQlip l ⟨le_rfl, hlh.le⟩ x hx
    simpa only [hQl, sub_zero, abs_of_pos hQx,
      abs_of_nonneg (sub_nonneg.mpr hx.1)] using hb
  have hright : Q x ≤ M * (h - x) := by
    have hb := hQlip h ⟨hlh.le, le_rfl⟩ x hx
    rw [hQh, sub_zero, abs_of_pos hQx, abs_sub_comm x h,
      abs_of_nonneg (sub_nonneg.mpr hx.2)] at hb
    exact hb
  let δ := q / (4 * (M + 1))
  have hMone : 0 < M + 1 := by linarith
  have hδ : 0 < δ := div_pos hq (mul_pos (by norm_num) hMone)
  have hδM : δ * M ≤ q / 4 := by
    have heq : δ * (M + 1) = q / 4 := by
      dsimp only [δ]
      rw [← div_div, div_mul_cancel₀ _ hMone.ne']
    exact (mul_le_mul_of_nonneg_left (by linarith : M ≤ M + 1) hδ.le).trans heq.le
  have hleftδ : l < x - δ := by
    by_contra hn
    have hdist : x - l ≤ δ := by linarith
    have hp := (mul_le_mul_of_nonneg_left hdist hM).trans
      (show M * δ ≤ q / 4 by simpa only [mul_comm] using hδM)
    linarith
  have hrightδ : x + δ < h := by
    by_contra hn
    have hdist : h - x ≤ δ := by linarith
    have hp := (mul_le_mul_of_nonneg_left hdist hM).trans
      (show M * δ ≤ q / 4 by simpa only [mul_comm] using hδM)
    linarith
  refine ⟨x, hδ, hleftδ, hrightδ, ?_⟩
  intro r hr
  have hrcc : r ∈ Icc l h := ⟨hleftδ.le.trans hr.1, hr.2.trans hrightδ.le⟩
  have hdist : |r - x| ≤ δ := by
    apply abs_le.mpr
    constructor <;> linarith [hr.1, hr.2]
  have hQr : |Q r - Q x| ≤ q / 4 :=
    (hQlip x hx r hrcc).trans ((mul_le_mul_of_nonneg_left hdist hM).trans
      (show M * δ ≤ q / 4 by simpa only [mul_comm] using hδM))
  have hQlower : (s / 2) ^ 2 ≤ Q r := by
    have hlow := (abs_le.mp hQr).1
    dsimp only [q] at hqmax hlow
    nlinarith [sq_nonneg s]
  have hQnonneg : 0 ≤ Q r := (sq_nonneg (s / 2)).trans hQlower
  have hspeed : s / 2 ≤ opticalSpeed w r := by
    have hsq : opticalSpeed w r ^ 2 = Q r := Real.sq_sqrt hQnonneg
    have hnonneg : 0 ≤ opticalSpeed w r := Real.sqrt_nonneg _
    nlinarith
  calc
    τ / (2 * (h - l)) = s / 2 := by
      dsimp only [s]
      rw [div_div]
      congr 1
      ring
    _ ≤ opticalSpeed w r := hspeed

end ContinuousFlexibility.Statements
