import ContinuousFlexibility.Analysis.PositiveEndpointCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Endpoint mass estimates for positive interpolation

A clipped endpoint field contributes at most its collar bound times the
collar width to the interval integral. These estimates make the numerator
and denominator of the reference interpolation normalizer positive by
an actual choice of a small radius; no lower bound on component widths is
required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- One oriented statement handles both endpoints: the integral starts at
the cutoff center, and the other limit may lie on either side. -/
theorem abs_integral_positiveEndpointCutoff_mul
    {c d δ M : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Metric.ball c δ, ContDiffAt ℝ ∞ f x)
    (hbound : ∀ x ∈ Metric.ball c δ, |f x| ≤ M) :
    |∫ x in c..d, positiveEndpointCutoff c δ x * f x| ≤ M * δ := by
  have hc := (contDiff_positiveEndpointCutoff_mul hδ hf).continuous
  have hb (x : ℝ) :
      ‖positiveEndpointCutoff c δ x * f x‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using
      abs_positiveEndpointCutoff_mul_le hδ hM hbound x
  by_cases hfar : δ ≤ |d - c|
  · let k : ℝ := if c ≤ d then c + δ else c - δ
    have hlength : |k - c| = δ := by
      dsimp only [k]
      split_ifs
      · simp only [add_sub_cancel_left, abs_of_pos hδ]
      · have he : c - δ - c = -δ := by ring
        rw [he, abs_neg, abs_of_pos hδ]
    have htail : (∫ x in k..d,
        positiveEndpointCutoff c δ x * f x) = 0 := by
      calc
        _ = ∫ _ in k..d, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hxout : x ∉ Metric.ball c δ := by
            by_cases hcd : c ≤ d
            · have hdc : 0 ≤ d - c := sub_nonneg.mpr hcd
              rw [abs_of_nonneg hdc] at hfar
              have hkd : c + δ ≤ d := by linarith
              have hx' : x ∈ Icc (c + δ) d := by
                simpa only [k, if_pos hcd, uIcc_of_le hkd] using hx
              rw [Metric.mem_ball, Real.dist_eq,
                abs_of_nonneg (by linarith [hx'.1] : 0 ≤ x - c)]
              linarith [hx'.1]
            · have hdc : d ≤ c := (lt_of_not_ge hcd).le
              rw [abs_of_nonpos (sub_nonpos.mpr hdc)] at hfar
              have hdk : d ≤ c - δ := by linarith
              have hx' : x ∈ Icc d (c - δ) := by
                rw [uIcc_comm] at hx
                simpa only [k, if_neg hcd, uIcc_of_le hdk] using hx
              rw [Metric.mem_ball, Real.dist_eq,
                abs_of_nonpos (by linarith [hx'.2] : x - c ≤ 0)]
              linarith [hx'.2]
          rw [positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hxout, zero_mul]
        _ = 0 := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable c k) (hc.intervalIntegrable k d)
    rw [htail, add_zero] at hsplit
    rw [← hsplit]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c) (b := k) (C := M)
      (f := fun x => positiveEndpointCutoff c δ x * f x) (fun x _ => hb x)
    simpa only [Real.norm_eq_abs, hlength] using hnorm
  · have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c) (b := d) (C := M)
      (f := fun x => positiveEndpointCutoff c δ x * f x) (fun x _ => hb x)
    have hnorm' : |∫ x in c..d, positiveEndpointCutoff c δ x * f x| ≤
        M * |d - c| := by
      simpa only [Real.norm_eq_abs] using hnorm
    exact hnorm'.trans
      (mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hfar)) hM)

/-- The unused middle portion has a positive total mass once the two
collars occupy less than the interval width. -/
theorem integral_positiveEndpointCutoff_complement_lower
    {l r δ : ℝ} (hδ : 0 < δ) :
    r - l - 2 * δ ≤
      ∫ x in l..r,
        (1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x) := by
  have hleft : |∫ x in l..r, positiveEndpointCutoff l δ x| ≤ δ := by
    simpa only [mul_one, one_mul] using
      (abs_integral_positiveEndpointCutoff_mul
        (c := l) (d := r) (M := 1) (f := fun _ => (1 : ℝ)) hδ (by norm_num)
        (fun _ _ => contDiffAt_const) (fun _ _ => by norm_num))
  have hright : |∫ x in l..r, positiveEndpointCutoff r δ x| ≤ δ := by
    have h := abs_integral_positiveEndpointCutoff_mul
      (c := r) (d := l) (M := 1) (f := fun _ => (1 : ℝ)) hδ (by norm_num)
      (fun _ _ => contDiffAt_const) (fun _ _ => by norm_num)
    rw [intervalIntegral.integral_symm, abs_neg] at h
    simpa only [mul_one, one_mul] using h
  have hL := (contDiff_positiveEndpointCutoff l δ).continuous.intervalIntegrable l r
  have hR := (contDiff_positiveEndpointCutoff r δ).continuous.intervalIntegrable l r
  rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub hL) hR,
    intervalIntegral.integral_sub intervalIntegrable_const hL,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  have hL' := le_trans (le_abs_self _) hleft
  have hR' := le_trans (le_abs_self _) hright
  linarith

theorem integral_positiveEndpointCutoff_complement_pos
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) :
    0 < ∫ x in l..r,
      (1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x) := by
  have h := integral_positiveEndpointCutoff_complement_lower (l := l) (r := r) hδ
  linarith

end ContinuousFlexibility.Analysis
