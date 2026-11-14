module

public import ContinuousFlexibility.Radial.PositiveBufferComparisonAffine
public import ContinuousFlexibility.Radial.PositiveBufferGeometry

/-!
# Analytic changes to the common buffer coordinate

The inward coordinate is the existing `positiveBufferPoint`.  This file
specializes the affine calculus and energy substitution to that coordinate
and records its inverse, so the same construction applies at both cuts.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open ContinuousFlexibility.Statements

theorem positiveBufferPoint_affine (B : BufferData) (i : Fin 2) (t : ℝ) :
    positiveBufferPoint B i t =
      bufferCut B i + (-bufferSign i / B.mass i) * t := by
  unfold positiveBufferPoint
  ring

theorem positiveBufferPoint_outward_affine (B : BufferData) (i : Fin 2) (t : ℝ) :
    positiveBufferPoint B i (-t) =
      bufferCut B i + (bufferSign i / B.mass i) * t := by
  unfold positiveBufferPoint
  ring

theorem positiveBufferPoint_slope_sq (B : BufferData) (i : Fin 2) :
    (-bufferSign i / B.mass i) ^ 2 = 1 / B.mass i ^ 2 := by
  rw [div_pow, neg_sq, bufferSign_sq]

theorem positiveBufferPoint_abs_slope {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) :
    |-bufferSign i / B.mass i| = 1 / B.mass i := by
  rw [abs_div, abs_neg, abs_bufferSign, abs_of_pos (buffer_mass_pos hB i)]

theorem positiveBufferPoint_slope_ne_zero {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) :
    -bufferSign i / B.mass i ≠ 0 := by
  apply div_ne_zero _ (buffer_mass_pos hB i).ne'
  intro h
  have hs := abs_bufferSign i
  rw [neg_eq_zero.mp h, abs_zero] at hs
  norm_num at hs

/-- The inverse of the inward buffer parametrization. -/
def positiveBufferCoordinate (B : BufferData) (i : Fin 2) (x : ℝ) : ℝ :=
  -bufferSign i * B.mass i * (x - bufferCut B i)

theorem positiveBufferCoordinate_affine (B : BufferData) (i : Fin 2) (x : ℝ) :
    positiveBufferCoordinate B i x =
      bufferSign i * B.mass i * bufferCut B i + (-bufferSign i * B.mass i) * x := by
  unfold positiveBufferCoordinate
  ring

theorem positiveBufferCoordinate_abs_slope {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) :
    |-bufferSign i * B.mass i| = B.mass i := by
  rw [abs_mul, abs_neg, abs_bufferSign, one_mul, abs_of_pos (buffer_mass_pos hB i)]

theorem positiveBufferCoordinate_slope_ne_zero {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) : -bufferSign i * B.mass i ≠ 0 := by
  apply abs_ne_zero.mp
  rw [positiveBufferCoordinate_abs_slope hB i]
  exact (buffer_mass_pos hB i).ne'

@[simp] theorem positiveBufferCoordinate_cut (B : BufferData) (i : Fin 2) :
    positiveBufferCoordinate B i (bufferCut B i) = 0 := by
  simp only [positiveBufferCoordinate, sub_self, mul_zero]

@[simp] theorem positiveBufferCoordinate_point {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (t : ℝ) :
    positiveBufferCoordinate B i (positiveBufferPoint B i t) = t := by
  have hm : B.mass i ≠ 0 := (buffer_mass_pos hB i).ne'
  calc
    _ = bufferSign i ^ 2 * t := by
      unfold positiveBufferCoordinate positiveBufferPoint
      field_simp [hm]
      <;> ring
    _ = t := by rw [bufferSign_sq, one_mul]

@[simp] theorem positiveBufferPoint_coordinate {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (x : ℝ) :
    positiveBufferPoint B i (positiveBufferCoordinate B i x) = x := by
  have hm : B.mass i ≠ 0 := (buffer_mass_pos hB i).ne'
  calc
    _ = bufferCut B i + bufferSign i ^ 2 * (x - bufferCut B i) := by
      unfold positiveBufferCoordinate positiveBufferPoint
      field_simp [hm]
      <;> ring
    _ = x := by rw [bufferSign_sq]; ring

theorem positiveBufferPoint_hasDerivAt {B : BufferData} {i : Fin 2}
    {u : ℝ → ℝ} {t d : ℝ} (hu : HasDerivAt u d (positiveBufferPoint B i t)) :
    HasDerivAt (fun s => u (positiveBufferPoint B i s))
      ((-bufferSign i / B.mass i) * d) t := by
  simpa only [← positiveBufferPoint_affine] using
    positiveBuffer_affine_hasDerivAt
      (a := bufferCut B i) (b := -bufferSign i / B.mass i)
      (by simpa only [← positiveBufferPoint_affine] using hu)

theorem positiveBufferPoint_homogeneous {B : BufferData} {i : Fin 2}
    {J : Set ℝ} {u du : ℝ → ℝ}
    (hu : ∀ x ∈ J, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ J, HasDerivAt du (B.potential x * u x) x)
    {t : ℝ} (ht : positiveBufferPoint B i t ∈ J) :
    HasDerivAt (fun s => u (positiveBufferPoint B i s))
        ((-bufferSign i / B.mass i) * du (positiveBufferPoint B i t)) t ∧
      HasDerivAt (fun s => (-bufferSign i / B.mass i) * du (positiveBufferPoint B i s))
        ((B.potential (positiveBufferPoint B i t) / B.mass i ^ 2) *
          u (positiveBufferPoint B i t)) t := by
  have h := positiveBuffer_affine_homogeneous hu hdu
    (bufferCut B i) (-bufferSign i / B.mass i)
    (by simpa only [← positiveBufferPoint_affine] using ht)
  simp only [← positiveBufferPoint_affine, positiveBufferPoint_slope_sq] at h
  have hcoeff (x : ℝ) : (1 / B.mass i ^ 2) * B.potential x =
      B.potential x / B.mass i ^ 2 := by ring
  simpa only [hcoeff] using h

theorem positiveBufferPoint_mem_openSpan {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {t : ℝ}
    (ht : t ∈ Ioo 0 (B.action i + 6)) :
    positiveBufferPoint B i t ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i) := by
  let b : ℝ := -bufferSign i / B.mass i
  have hpoint : positiveBufferPoint B i t = bufferCut B i + b * t :=
    positiveBufferPoint_affine B i t
  have hwall : bufferInnerWall B i = bufferCut B i + b * (B.action i + 6) := by
    rw [← positiveBufferPoint_innerWall, positiveBufferPoint_affine]
  have hb : b ≠ 0 := positiveBufferPoint_slope_ne_zero hB i
  change min (bufferCut B i) (bufferInnerWall B i) < positiveBufferPoint B i t ∧
    positiveBufferPoint B i t < max (bufferCut B i) (bufferInnerWall B i)
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hlt : positiveBufferPoint B i t < bufferCut B i := by
      rw [hpoint]
      nlinarith [mul_neg_of_neg_of_pos hbneg ht.1]
    have hgt : bufferInnerWall B i < positiveBufferPoint B i t := by
      rw [hpoint, hwall]
      linarith [mul_lt_mul_of_neg_left ht.2 hbneg]
    exact ⟨(min_le_right _ _).trans_lt hgt, hlt.trans_le (le_max_left _ _)⟩
  · have hgt : bufferCut B i < positiveBufferPoint B i t := by
      rw [hpoint]
      exact lt_add_of_pos_right _ (mul_pos hbpos ht.1)
    have hlt : positiveBufferPoint B i t < bufferInnerWall B i := by
      rw [hpoint, hwall]
      linarith [mul_lt_mul_of_pos_left ht.2 hbpos]
    exact ⟨(min_le_left _ _).trans_lt hgt, hlt.trans_le (le_max_right _ _)⟩

theorem positiveBufferPoint_normalized_potential_lower {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {t : ℝ}
    (ht : t ≤ B.action i + 6) :
    1 ≤ B.potential (positiveBufferPoint B i t) / B.mass i ^ 2 := by
  exact (one_le_div (sq_pos_of_pos (buffer_mass_pos hB i))).2
    (positiveBufferPoint_potential_lower hB i ht)

theorem positiveBufferPoint_normalized_potential_upper_cut {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {t : ℝ} (ht : |t| ≤ 4) :
    B.potential (positiveBufferPoint B i t) / B.mass i ^ 2 ≤ B.layerBound := by
  exact (div_le_iff₀ (sq_pos_of_pos (buffer_mass_pos hB i))).2
    (positiveBufferPoint_potential_upper_cut hB i ht)

/-- The inverse Jacobian from physical length to normalized length. -/
theorem positiveBufferPoint_setIntegral {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (f : ℝ → ℝ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ t in (positiveBufferPoint B i) ⁻¹' s, f (positiveBufferPoint B i t)) =
      B.mass i * ∫ x in s, f x := by
  simpa only [← positiveBufferPoint_affine, positiveBufferPoint_abs_slope hB i,
    one_div, inv_inv] using
    positiveBuffer_affine_setIntegral f hs (bufferCut B i) (-bufferSign i / B.mass i)

/-- Normalized energy equals physical energy divided by the mass. -/
theorem positiveBufferPoint_energy_change {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {s : Set ℝ} (hs : MeasurableSet s)
    (u du : ℝ → ℝ) :
    (∫ t in (positiveBufferPoint B i) ⁻¹' s,
      ((-bufferSign i / B.mass i) * du (positiveBufferPoint B i t)) ^ 2 +
        (B.potential (positiveBufferPoint B i t) / B.mass i ^ 2) *
          u (positiveBufferPoint B i t) ^ 2) =
      (1 / B.mass i) * ∫ x in s, du x ^ 2 + B.potential x * u x ^ 2 := by
  have h := positiveBuffer_affine_energy_change hs u du B.potential
    (bufferCut B i) (positiveBufferPoint_slope_ne_zero hB i)
  simp only [← positiveBufferPoint_affine, positiveBufferPoint_slope_sq,
    positiveBufferPoint_abs_slope hB i] at h
  have hcoeff (x : ℝ) : (1 / B.mass i ^ 2) * B.potential x =
      B.potential x / B.mass i ^ 2 := by ring
  simpa only [hcoeff] using h

end ContinuousFlexibility.Radial
