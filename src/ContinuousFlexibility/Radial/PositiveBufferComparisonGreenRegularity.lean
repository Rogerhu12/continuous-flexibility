import ContinuousFlexibility.Radial.PositiveBufferComparisonGreenError

/-!
# Smooth physical cutoff data

The source is globally smooth and compactly supported. On the retained
interval the Green kernel equals one globally smooth interior formula,
including both finite endpoint traces.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem positiveBufferPoint_contDiff (B : BufferData) (i : Fin 2) :
    ContDiff ℝ ∞ (positiveBufferPoint B i) := by
  simpa only [← positiveBufferPoint_affine] using
    (contDiff_const.add (contDiff_const.mul contDiff_id) :
      ContDiff ℝ ∞ (fun t : ℝ => bufferCut B i + (-bufferSign i / B.mass i) * t))

theorem positiveBufferCoordinate_contDiff (B : BufferData) (i : Fin 2) :
    ContDiff ℝ ∞ (positiveBufferCoordinate B i) := by
  simpa only [← positiveBufferCoordinate_affine] using
    (contDiff_const.add (contDiff_const.mul contDiff_id) : ContDiff ℝ ∞
      (fun x : ℝ => bufferSign i * B.mass i * bufferCut B i + (-bufferSign i * B.mass i) * x))

theorem positiveBufferCutoffError_contDiff (σ : ℝ) {u du : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hdu : ContDiff ℝ ∞ du) :
    ContDiff ℝ ∞ (positiveBufferCutoffError σ u du) := by
  have hχ' := (contDiff_infty_iff_deriv.mp (positiveBufferCutoff_contDiff σ)).2
  have hχ'' := (contDiff_infty_iff_deriv.mp hχ').2
  exact (hχ''.neg.mul hu).sub ((contDiff_const.mul hχ').mul hdu)

theorem positiveBufferGreenError_contDiff (B : BufferData) (i : Fin 2) (A : ℝ)
    {pin dpin : ℝ → ℝ} (hpin : ContDiff ℝ ∞ pin) (hdpin : ContDiff ℝ ∞ dpin) :
    ContDiff ℝ ∞ (positiveBufferGreenError B i A pin dpin) := by
  exact contDiff_const.mul
    ((positiveBufferCutoffError_contDiff (B.action i) hpin hdpin).comp
      (positiveBufferCoordinate_contDiff B i))

theorem positiveBufferGreenError_hasCompactSupport {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (A : ℝ) (pin dpin : ℝ → ℝ) :
    HasCompactSupport (positiveBufferGreenError B i A pin dpin) := by
  apply HasCompactSupport.intro
    ((isCompact_Icc : IsCompact (Icc (B.action i + 2) (B.action i + 4))).image
      (positiveBufferPoint_contDiff B i).continuous)
  intro x hx
  by_contra hn
  have ht := positiveBufferGreenError_support B i A pin dpin hn
  apply hx
  exact ⟨positiveBufferCoordinate B i x, ht, positiveBufferPoint_coordinate hB i x⟩

/-- The interior expression extends smoothly across either retained cut. -/
def positiveBufferGreenInterior (B : BufferData) (i : Fin 2) (A : ℝ)
    (pin : ℝ → ℝ) (x : ℝ) : ℝ :=
  A⁻¹ * (positiveBufferCutoff (B.action i) (positiveBufferCoordinate B i x) *
    pin (positiveBufferCoordinate B i x))

theorem positiveBufferGreenInterior_contDiff (B : BufferData) (i : Fin 2) (A : ℝ)
    {pin : ℝ → ℝ} (hpin : ContDiff ℝ ∞ pin) :
    ContDiff ℝ ∞ (positiveBufferGreenInterior B i A pin) := by
  exact contDiff_const.mul
    (((positiveBufferCutoff_contDiff (B.action i)).mul hpin).comp
      (positiveBufferCoordinate_contDiff B i))

theorem positiveBufferGreenProfile_eq_interior {σ t : ℝ} {pin pout : ℝ → ℝ}
    (hσ : 0 < σ) (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1) (ht : 0 ≤ t) :
    positiveBufferGreenProfile σ pin pout t = positiveBufferCutoff σ t * pin t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [positiveBufferGreenProfile_cut hpout0, positiveBufferCutoff_one (by linarith),
      hpin0, mul_one]
  · exact bufferCutGlue_of_lt 0 _ _ ht

theorem positiveBufferCoordinate_nonneg_interval {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {x : ℝ} (hx : x ∈ Icc B.l B.h) :
    0 ≤ positiveBufferCoordinate B i x := by
  have hm := buffer_mass_pos hB i
  by_cases hi : i = 0
  · simp only [positiveBufferCoordinate, bufferCut, bufferSign, hi, ite_true,
      neg_neg, one_mul]
    simpa only [hi] using mul_nonneg hm.le (sub_nonneg.mpr hx.1)
  · simp only [positiveBufferCoordinate, bufferCut, bufferSign, hi, ite_false,
      neg_mul, one_mul]
    have hmul := mul_nonpos_of_nonneg_of_nonpos hm.le (sub_nonpos.mpr hx.2)
    nlinarith

theorem positiveBufferGreenKernel_eq_interior {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (A : ℝ) {pin pout : ℝ → ℝ}
    (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1) {x : ℝ} (hx : x ∈ Icc B.l B.h) :
    positiveBufferGreenKernel B i A pin pout x = positiveBufferGreenInterior B i A pin x := by
  unfold positiveBufferGreenKernel positiveBufferGreenInterior
  rw [positiveBufferGreenProfile_eq_interior (buffer_action_pos hB i) hpin0 hpout0
    (positiveBufferCoordinate_nonneg_interval hB i hx)]

/-- The entire normalized Green kernel lies in the positive end region,
where the actual compact scalar border vanishes. -/
theorem positiveBufferGreenKernel_border_zero {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (A : ℝ) (pin pout : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Function.support (positiveBufferGreenKernel B i A pin pout)) :
    B.borderFunction x = 0 := by
  have ht : positiveBufferCoordinate B i x < B.action i + 4 := by
    by_contra hn
    have hz := positiveBufferGreenProfile_zero (pin := pin) (pout := pout)
      (buffer_action_pos hB i) (le_of_not_gt hn)
    apply hx
    simp only [positiveBufferGreenKernel, hz, mul_zero]
  have hz := positiveBufferPoint_border_eq_zero hB i
    (t := positiveBufferCoordinate B i x) (by linarith)
  rwa [positiveBufferPoint_coordinate hB i x] at hz

end ContinuousFlexibility.Radial
