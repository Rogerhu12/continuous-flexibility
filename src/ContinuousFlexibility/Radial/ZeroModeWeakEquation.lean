import ContinuousFlexibility.Radial.ZeroModeL1Primitive
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The zero-mode equation for an integrable source

These identities concern the actual integral primitives. The weak
equation holds for every smooth test compactly inside the radial interval,
assuming only integrability of the source and of its flux divided by the
profile. In particular, the source need not have a continuous representative.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem zeroModeFlux_eq_neg_right_of_integrable
    {a b r : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hmean : (∫ t in a..b, f t) = 0)
    (hr : r ∈ Icc a b) :
    zeroModeFlux a f r = -(∫ t in r..b, f t) := by
  have hab : a ≤ b := hr.1.trans hr.2
  have hleft : IntervalIntegrable f volume a r := hf.mono_set (by
    rw [uIcc_of_le hr.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hr.2)
  have hright : IntervalIntegrable f volume r b := hf.mono_set (by
    rw [uIcc_of_le hr.2, uIcc_of_le hab]
    exact Icc_subset_Icc hr.1 le_rfl)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hleft hright
  change (∫ t in a..r, f t) = -(∫ t in r..b, f t)
  rw [hmean] at hsum
  linarith

/-- The true maximal weak equation for the two integral primitives. -/
theorem zeroModeHeight_weak_of_integrable
    {a b : ℝ} (hab : a < b) {w f : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ r ∈ Ioo a b, w r ≠ 0)
    (hf : IntervalIntegrable f volume a b)
    (hq : IntervalIntegrable (fun r => zeroModeFlux a f r / w r) volume a b)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    (∫ r in a..b, zeroModeHeight a b w f r *
      deriv (fun t => w t * deriv ψ t) r) =
      ∫ r in a..b, f r * ψ r := by
  have hψb : ψ b = 0 := by
    by_contra hn
    exact (lt_irrefl b) (hψs (subset_tsupport ψ hn)).2
  have hdψa : deriv ψ a = 0 := by
    by_contra hn
    have ha : a ∈ tsupport ψ :=
      tsupport_deriv_subset (subset_tsupport (deriv ψ) hn)
    exact (lt_irrefl a) (hψs ha).1
  have hφ : ContDiff ℝ ∞ (fun t => w t * deriv ψ t) :=
    hw.mul (contDiff_infty_iff_deriv.mp hψ).2
  have hU := zeroModeHeight_integral_mul_deriv hq
    ((hφ.of_le (by simp)).contDiffOn)
  have hP := intervalPrimitive_integral_mul_deriv hf
    ((hψ.of_le (by simp)).contDiffOn)
  change (∫ r in a..b, zeroModeFlux a f r * deriv ψ r) =
    zeroModeFlux a f b * ψ b - ∫ r in a..b, f r * ψ r at hP
  rw [hψb, mul_zero, zero_sub] at hP
  have hcancel :
      (∫ r in a..b, (zeroModeFlux a f r / w r) * (w r * deriv ψ r)) =
        ∫ r in a..b, zeroModeFlux a f r * deriv ψ r := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_neq b] with r hrb hr
    rw [uIoc_of_le hab.le] at hr
    have hri : r ∈ Ioo a b := ⟨hr.1, lt_of_le_of_ne hr.2 hrb⟩
    calc
      (zeroModeFlux a f r / w r) * (w r * deriv ψ r) =
          ((zeroModeFlux a f r / w r) * w r) * deriv ψ r := by ring
      _ = zeroModeFlux a f r * deriv ψ r := by
        rw [div_mul_cancel₀ _ (hwn r hri)]
  calc
    (∫ r in a..b, zeroModeHeight a b w f r *
        deriv (fun t => w t * deriv ψ t) r) =
        -(∫ r in a..b, (zeroModeFlux a f r / w r) * (w r * deriv ψ r)) := by
      simpa only [hdψa, mul_zero, neg_zero, zero_sub] using hU
    _ = -(∫ r in a..b, zeroModeFlux a f r * deriv ψ r) := congrArg Neg.neg hcancel
    _ = ∫ r in a..b, f r * ψ r := by rw [hP, neg_neg]

theorem zeroModeHeight_weak_radialJacobi
    {a b : ℝ} (hab : a < b) {w f : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ r ∈ Ioo a b, w r ≠ 0)
    (hf : IntervalIntegrable f volume a b)
    (hq : IntervalIntegrable (fun r => zeroModeFlux a f r / w r) volume a b)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    (∫ r in a..b, zeroModeHeight a b w f r * radialJacobi 0 w ψ r) =
      ∫ r in a..b, f r * ψ r := by
  simpa only [radialJacobi, zero_mul, zero_div, sub_zero] using
    zeroModeHeight_weak_of_integrable hab hw hwn hf hq hψ hψs

end ContinuousFlexibility.Radial
