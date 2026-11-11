import ContinuousFlexibility.Radial.PositiveBufferComparisonCoordinates

/-!
# Domains in the common inward buffer coordinate

The exterior corresponds to negative normalized coordinates. Reflecting
that coordinate gives the positive half-line used in the ODE comparison.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

theorem positiveBufferPoint_preimage_exterior {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) :
    (positiveBufferPoint B i) ⁻¹' bufferExterior B i = Iio 0 := by
  ext t
  have hm := buffer_mass_pos hB i
  have he : positiveBufferPoint B i t ∈ bufferExterior B i ↔ t / B.mass i < 0 := by
    by_cases hi : i = 0 <;>
      simp only [positiveBufferPoint, bufferExterior, bufferCut, bufferSign, hi,
        ite_true, ite_false, neg_mul, one_mul, neg_div, sub_neg_eq_add, mem_Iio, mem_Ioi] <;>
      constructor <;> intro h <;> linarith
  exact he.trans (by
    simpa only [mem_Iio, zero_mul] using
      (div_lt_iff₀ hm : t / B.mass i < 0 ↔ t < 0 * B.mass i))

theorem positiveBufferPoint_preimage_exterior_closure {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) :
    (positiveBufferPoint B i) ⁻¹' closure (bufferExterior B i) = Iic 0 := by
  ext t
  have hm := buffer_mass_pos hB i
  have he : positiveBufferPoint B i t ∈ closure (bufferExterior B i) ↔
      t / B.mass i ≤ 0 := by
    by_cases hi : i = 0 <;>
      simp only [positiveBufferPoint, bufferExterior, bufferCut, bufferSign, hi,
        ite_true, ite_false, neg_mul, one_mul, neg_div, sub_neg_eq_add,
        closure_Iio, closure_Ioi, mem_Iic, mem_Ici] <;>
      constructor <;> intro h <;> linarith
  exact he.trans (by
    simpa only [mem_Iic, zero_mul] using
      (div_le_iff₀ hm : t / B.mass i ≤ 0 ↔ t ≤ 0 * B.mass i))

theorem positiveBufferPoint_outward_preimage_exterior {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) :
    (fun t : ℝ => positiveBufferPoint B i (-t)) ⁻¹' bufferExterior B i = Ioi 0 := by
  have heq := congrArg (fun s : Set ℝ => (fun t : ℝ => -t) ⁻¹' s)
    (positiveBufferPoint_preimage_exterior hB i)
  simpa only [preimage_preimage, Function.comp_def, neg_preimage, neg_Iio, neg_zero] using heq

theorem positiveBufferPoint_outward_preimage_exterior_closure {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) :
    (fun t : ℝ => positiveBufferPoint B i (-t)) ⁻¹' closure (bufferExterior B i) = Ici 0 := by
  have heq := congrArg (fun s : Set ℝ => (fun t : ℝ => -t) ⁻¹' s)
    (positiveBufferPoint_preimage_exterior_closure hB i)
  simpa only [preimage_preimage, Function.comp_def, neg_preimage, neg_Iic, neg_zero] using heq

theorem positiveBuffer_affine_preimage_uIcc {a b L : ℝ} (hb : b ≠ 0) (hL : 0 ≤ L) :
    (fun t : ℝ => a + b * t) ⁻¹' uIcc a (a + b * L) = Icc 0 L := by
  ext t
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hend : a + b * L ≤ a := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hbneg.le hL]
    simp only [mem_preimage, uIcc_of_ge hend, mem_Icc]
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor
      · by_contra ht
        have hp := mul_pos_of_neg_of_neg hbneg (lt_of_not_ge ht)
        linarith
      · by_contra ht
        have hp := mul_lt_mul_of_neg_left (lt_of_not_ge ht) hbneg
        linarith
    · rintro ⟨hlo, hhi⟩
      exact ⟨by linarith [mul_le_mul_of_nonpos_left hhi hbneg.le],
        by nlinarith [mul_nonpos_of_nonpos_of_nonneg hbneg.le hlo]⟩
  · have hend : a ≤ a + b * L := by nlinarith [mul_nonneg hbpos.le hL]
    simp only [mem_preimage, uIcc_of_le hend, mem_Icc]
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor
      · exact (mul_nonneg_iff_of_pos_left hbpos).mp (by linarith)
      · exact (mul_le_mul_iff_right₀ hbpos).mp (by linarith)
    · rintro ⟨hlo, hhi⟩
      exact ⟨by nlinarith [mul_nonneg hbpos.le hlo],
        by linarith [mul_le_mul_of_nonneg_left hhi hbpos.le]⟩

theorem positiveBufferPoint_preimage_span {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) :
    (positiveBufferPoint B i) ⁻¹' uIcc (bufferCut B i) (bufferInnerWall B i) =
      Icc 0 (B.action i + 6) := by
  have ha := buffer_action_pos hB i
  have hw : bufferInnerWall B i =
      bufferCut B i + (-bufferSign i / B.mass i) * (B.action i + 6) := by
    rw [← positiveBufferPoint_innerWall, positiveBufferPoint_affine]
  have hp : positiveBufferPoint B i =
      fun t : ℝ => bufferCut B i + (-bufferSign i / B.mass i) * t :=
    funext (positiveBufferPoint_affine B i)
  rw [hp, hw]
  exact positiveBuffer_affine_preimage_uIcc (a := bufferCut B i)
    (b := -bufferSign i / B.mass i) (L := B.action i + 6)
    (positiveBufferPoint_slope_ne_zero hB i) (by linarith)

theorem positiveBufferPoint_before_innerWall {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {t : ℝ} (ht : t ≤ B.action i + 6) :
    if i = 0 then positiveBufferPoint B i t ≤ bufferInnerWall B i
    else bufferInnerWall B i ≤ positiveBufferPoint B i t := by
  have hm := buffer_mass_pos hB i
  have hdiv := (div_le_div_iff_of_pos_right hm).2 ht
  by_cases hi : i = 0
  · simp only [hi, ite_true, positiveBufferPoint, bufferInnerWall, bufferCut, bufferSign,
      neg_mul, one_mul, neg_div, sub_neg_eq_add]
    simpa only [hi, add_comm] using add_le_add_left hdiv B.l
  · simp only [hi, ite_false, positiveBufferPoint, bufferInnerWall, bufferCut, bufferSign, one_mul]
    exact sub_le_sub_left hdiv B.h

/-- The two positive end regions are separated by the strictly ordered
inner walls. This includes both exterior half-lines. -/
theorem positiveBufferPoint_end_regions_disjoint {B : BufferData}
    (hB : BufferHypotheses B) {i j : Fin 2} (hij : i ≠ j)
    {s t : ℝ} (hs : s ≤ B.action i + 6) (ht : t ≤ B.action j + 6) :
    positiveBufferPoint B i s ≠ positiveBufferPoint B j t := by
  have hi := positiveBufferPoint_before_innerWall hB i hs
  have hj := positiveBufferPoint_before_innerWall hB j ht
  have hw : bufferInnerWall B 0 < bufferInnerWall B 1 := hB.2.1
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · norm_num at hi hj
    intro heq
    change positiveBufferPoint B 0 s = positiveBufferPoint B 1 t at heq
    rw [heq] at hi
    linarith
  · norm_num at hi hj
    intro heq
    change positiveBufferPoint B 1 s = positiveBufferPoint B 0 t at heq
    rw [heq] at hi
    linarith
  · exact (hij rfl).elim

end ContinuousFlexibility.Radial
