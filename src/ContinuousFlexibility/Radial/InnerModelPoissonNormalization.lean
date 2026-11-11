import ContinuousFlexibility.Radial.InnerModelPoissonBound

/-!
# The actual physical cut normalization of model Poisson columns

The height and Liouville scale cancel against the physical kappa.
The velocity-to-mass bound controls the leading term. The remainder
retains its exact exponential envelope until the ordered choices make
its frequency multiple small.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem innerPhysicalCut_sqrt {height s k : ℝ}
    (hh : 0 < height) (hs : 0 < s) :
    sqrt (height * s ^ 2 * k) = (sqrt height * s) * sqrt k := by
  rw [sqrt_mul (mul_nonneg hh.le (sq_nonneg s)),
    sqrt_mul hh.le, sqrt_sq hs.le]

variable (D : ReferenceData) {B : BufferData} (hB : BufferHypotheses B)
  {C K : ℝ} (M : InnerBufferLocalizedData B C K)
  {R s : ℝ → ℝ} {height : ℝ}
  (hh : 0 < height) (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc B.l B.h, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R B.l) (R B.h) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc B.l B.h, D.w (R x) = height * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc B.l B.h, |deriv R x / R x| ≤ U)

theorem innerModelPhysicalPoissonColumn_normalized_bound
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (i : Fin 2) {ratio w Ucap k : ℝ}
    (hratio : 0 ≤ ratio) (hwpos : 0 < w) (hcap : 0 ≤ Ucap) (hk : 0 < k)
    (hcentral : B.bordered = true → w = 1)
    (hconstant : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i), W (R x) = w)
    (hbuffer : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i),
      |deriv R x / R x| ≤ Ucap)
    (hcell : ∀ x ∈ Ioo B.l B.h, |W (R x)| ≤ ratio * w) :
    ‖(w * sqrt (height * s (bufferCut B i) ^ 2 * k))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
        (innerModelPhysicalPoissonColumn D hB M hh hR hs hp hcore hw U hU hv i)‖ ≤
      sqrt 12 * (Ucap / B.mass i) * (sqrt (M.column i).inwardEnergy / sqrt k) +
        (sqrt 12 * U * ratio + 1) * (innerBufferRemainderEnvelope B C K i / sqrt k) := by
  have hcut : bufferCut B i ∈ Icc B.l B.h := by
    unfold bufferCut
    split_ifs
    · exact left_mem_Icc.mpr hB.1.le
    · exact right_mem_Icc.mpr hB.1.le
  have hsi := (hp _ hcut).2.2
  have hscale : 0 < sqrt height * s (bufferCut B i) := mul_pos (sqrt_pos.mpr hh) hsi
  have hroot : sqrt (height * s (bufferCut B i) ^ 2 * k) =
      (sqrt height * s (bufferCut B i)) * sqrt k := innerPhysicalCut_sqrt hh hsi
  have hden : 0 < w * sqrt (height * s (bufferCut B i) ^ 2 * k) := by
    rw [hroot]
    exact mul_pos hwpos (mul_pos hscale (sqrt_pos.mpr hk))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden)]
  calc
    _ ≤ (w * sqrt (height * s (bufferCut B i) ^ 2 * k))⁻¹ *
        ((sqrt height * s (bufferCut B i)) * w *
          (sqrt 12 * Ucap * (sqrt (M.column i).inwardEnergy / B.mass i) +
            (sqrt 12 * U * ratio + 1) * innerBufferRemainderEnvelope B C K i)) :=
      mul_le_mul_of_nonneg_left
        (innerModelPhysicalPoissonColumn_weighted_bound D hB M hh hR hs hp hcore hw U hU hv
          W hW CW hWC i hratio hwpos hcap hcentral hconstant hbuffer hcell)
        (inv_nonneg.mpr hden.le)
    _ = _ := by
      rw [hroot]
      field_simp [hwpos.ne', hscale.ne', (sqrt_pos.mpr hk).ne',
        (buffer_mass_pos hB i).ne']
      <;> ring

/-- This is the actual normalized column estimate used in the finite
assembly. The remaining envelope hypothesis is discharged uniformly by
the frequency-strengthened suppression, not by bounding a finite list
of frequencies. -/
theorem innerModelPhysicalPoissonColumn_frequency_bound
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (i : Fin 2) {ratio w Ucap k j Kcap : ℝ}
    (hratio : 0 ≤ ratio) (hwpos : 0 < w) (hcap : 0 ≤ Ucap) (hk : 0 < k)
    (hj : 0 < j) (hKcap : 0 ≤ Kcap)
    (hcentral : B.bordered = true → w = 1)
    (hconstant : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i), W (R x) = w)
    (hbuffer : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i),
      |deriv R x / R x| ≤ Ucap)
    (hcell : ∀ x ∈ Ioo B.l B.h, |W (R x)| ≤ ratio * w)
    (henergy : (M.column i).inwardEnergy ≤ 2 * k)
    (hvelocity : Ucap / B.mass i ≤ Kcap / j)
    (hremainder : (sqrt 12 * U * ratio + 1) *
      (innerBufferRemainderEnvelope B C K i / sqrt k) ≤ 1 / j) :
    ‖(w * sqrt (height * s (bufferCut B i) ^ 2 * k))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
        (innerModelPhysicalPoissonColumn D hB M hh hR hs hp hcore hw U hU hv i)‖ ≤
      (sqrt 12 * Kcap * sqrt 2 + 1) / j := by
  have he : sqrt (M.column i).inwardEnergy / sqrt k ≤ sqrt 2 := by
    apply (div_le_iff₀ (sqrt_pos.mpr hk)).mpr
    simpa only [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] using sqrt_le_sqrt henergy
  have hmain : sqrt 12 * (Ucap / B.mass i) *
      (sqrt (M.column i).inwardEnergy / sqrt k) ≤ sqrt 12 * (Kcap / j) * sqrt 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hvelocity (sqrt_nonneg 12)) he
      (div_nonneg (sqrt_nonneg _) (sqrt_nonneg k))
      (mul_nonneg (sqrt_nonneg 12) (div_nonneg hKcap hj.le))
  apply (innerModelPhysicalPoissonColumn_normalized_bound
    D hB M hh hR hs hp hcore hw U hU hv W hW CW hWC i
      hratio hwpos hcap hk hcentral hconstant hbuffer hcell).trans
  calc
    _ ≤ sqrt 12 * (Kcap / j) * sqrt 2 + 1 / j := add_le_add hmain hremainder
    _ = _ := by field_simp [hj.ne'] <;> ring

end ContinuousFlexibility.Radial
