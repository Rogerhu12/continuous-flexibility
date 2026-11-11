import ContinuousFlexibility.Radial.ZeroModePrimitive
import ContinuousFlexibility.Radial.IntervalWeakPrimitive
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The actual zero-mode primitives for integrable sources

The flux and height are the existing `zeroModeFlux` and `zeroModeHeight`.
An interval-integrable source gives an absolutely continuous flux. Once
its flux divided by the profile is integrable, the height is absolutely
continuous on the closed interval and C1 in its interior.

The integral identity uses the general L1 primitive theorem. No
approximation by smooth sources or endpoint trace assumption is used.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem zeroModeFlux_absolutelyContinuousOnInterval
    {a b : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) :
    AbsolutelyContinuousOnInterval (zeroModeFlux a f) a b := by
  exact hf.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)

theorem zeroModeFlux_continuousOn_of_integrable
    {a b : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) :
    ContinuousOn (zeroModeFlux a f) (uIcc a b) :=
  (zeroModeFlux_absolutelyContinuousOnInterval hf).continuousOn

/-- The right-normalized height is the same actual integral primitive,
with basepoint at the right endpoint. -/
theorem zeroModeHeight_eq_integral
    (a b : ℝ) (w f : ℝ → ℝ) (r : ℝ) :
    zeroModeHeight a b w f r =
      ∫ t in b..r, zeroModeFlux a f t / w t := by
  exact (intervalIntegral.integral_symm b r).symm

theorem zeroModeHeight_absolutelyContinuousOnInterval
    {a b : ℝ} {w f : ℝ → ℝ}
    (hq : IntervalIntegrable (fun r => zeroModeFlux a f r / w r) volume a b) :
    AbsolutelyContinuousOnInterval (zeroModeHeight a b w f) a b := by
  simpa only [← zeroModeHeight_eq_integral] using
    hq.absolutelyContinuousOnInterval_intervalIntegral (c := b) (by simp)

theorem zeroModeHeight_continuousOn_of_integrable
    {a b : ℝ} {w f : ℝ → ℝ}
    (hq : IntervalIntegrable (fun r => zeroModeFlux a f r / w r) volume a b) :
    ContinuousOn (zeroModeHeight a b w f) (uIcc a b) :=
  (zeroModeHeight_absolutelyContinuousOnInterval hq).continuousOn

theorem zeroModeQuot_continuousOn_of_integrable
    {a b : ℝ} {w f : ℝ → ℝ}
    (hw : ContinuousOn w (Ioo a b))
    (hwn : ∀ r ∈ Ioo a b, w r ≠ 0)
    (hf : IntervalIntegrable f volume a b) :
    ContinuousOn (fun r => zeroModeFlux a f r / w r) (Ioo a b) :=
  ((zeroModeFlux_continuousOn_of_integrable hf).mono
    (Ioo_subset_Icc_self.trans Icc_subset_uIcc)).div hw hwn

theorem zeroModeHeight_hasDerivAt_of_integrable
    {a b : ℝ} {w f : ℝ → ℝ}
    (hw : ContinuousOn w (Ioo a b))
    (hwn : ∀ r ∈ Ioo a b, w r ≠ 0)
    (hf : IntervalIntegrable f volume a b)
    (hq : IntervalIntegrable (fun r => zeroModeFlux a f r / w r) volume a b)
    {r : ℝ} (hr : r ∈ Ioo a b) :
    HasDerivAt (zeroModeHeight a b w f) (zeroModeFlux a f r / w r) r := by
  have hab : a ≤ b := hr.1.le.trans hr.2.le
  have hqr : IntervalIntegrable (fun t => zeroModeFlux a f t / w t) volume r b :=
    hq.mono_set (by
      rw [uIcc_of_le hr.2.le, uIcc_of_le hab]
      exact Icc_subset_Icc hr.1.le le_rfl)
  have hc := zeroModeQuot_continuousOn_of_integrable hw hwn hf
  have hd := (intervalIntegral.integral_hasDerivAt_left hqr
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hc r hr)
    (hc.continuousAt (isOpen_Ioo.mem_nhds hr))).neg
  simpa only [zeroModeHeight, Pi.neg_apply, neg_neg] using hd

theorem zeroModeHeight_flux_of_integrable
    {a b : ℝ} {w f : ℝ → ℝ}
    (hw : ContinuousOn w (Ioo a b))
    (hwn : ∀ r ∈ Ioo a b, w r ≠ 0)
    (hf : IntervalIntegrable f volume a b)
    (hq : IntervalIntegrable (fun r => zeroModeFlux a f r / w r) volume a b)
    {r : ℝ} (hr : r ∈ Ioo a b) :
    w r * deriv (zeroModeHeight a b w f) r = zeroModeFlux a f r := by
  rw [(zeroModeHeight_hasDerivAt_of_integrable hw hwn hf hq hr).deriv]
  simpa only [mul_comm] using div_mul_cancel₀ (zeroModeFlux a f r) (hwn r hr)

theorem zeroModeHeight_contDiffOn_one_of_integrable
    {a b : ℝ} {w f : ℝ → ℝ}
    (hw : ContinuousOn w (Ioo a b))
    (hwn : ∀ r ∈ Ioo a b, w r ≠ 0)
    (hf : IntervalIntegrable f volume a b)
    (hq : IntervalIntegrable (fun r => zeroModeFlux a f r / w r) volume a b) :
    ContDiffOn ℝ 1 (zeroModeHeight a b w f) (Ioo a b) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun r hr =>
    (zeroModeHeight_hasDerivAt_of_integrable hw hwn hf hq hr).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  apply (zeroModeQuot_continuousOn_of_integrable hw hwn hf).congr
  intro r hr
  exact (zeroModeHeight_hasDerivAt_of_integrable hw hwn hf hq hr).deriv

/-- Integration by parts for the actual height. The left endpoint value
is retained, so this identity also controls tests that do not vanish there. -/
theorem zeroModeHeight_integral_mul_deriv
    {a b : ℝ} {w f φ : ℝ → ℝ}
    (hq : IntervalIntegrable (fun r => zeroModeFlux a f r / w r) volume a b)
    (hφ : ContDiffOn ℝ 1 φ (uIcc a b)) :
    (∫ r in a..b, zeroModeHeight a b w f r * deriv φ r) =
      -(zeroModeHeight a b w f a * φ a) -
        ∫ r in a..b, (zeroModeFlux a f r / w r) * φ r := by
  have hU := zeroModeHeight_absolutelyContinuousOnInterval hq
  have h := hU.integral_mul_deriv_eq_deriv_mul hφ.absolutelyContinuousOnInterval
  have hfun : (fun r => ∫ t in b..r, zeroModeFlux a f t / w t) =
      zeroModeHeight a b w f :=
    funext (fun r => (zeroModeHeight_eq_integral a b w f r).symm)
  have hderiv :
      (∫ r in a..b, deriv (zeroModeHeight a b w f) r * φ r) =
        ∫ r in a..b, (zeroModeFlux a f r / w r) * φ r := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hq.ae_hasDerivAt_integral] with r hr hri
    have hd := hr (uIoc_subset_uIcc hri) b (by simp)
    rw [hfun] at hd
    rw [hd.deriv]
  have hb : zeroModeHeight a b w f b = 0 := by
    simp only [zeroModeHeight, intervalIntegral.integral_same, neg_zero]
  simpa only [hb, zero_mul, zero_sub, hderiv] using h

end ContinuousFlexibility.Radial
