import ContinuousFlexibility.Statements.RadialTargets

/-!
# The common oriented coordinate of the two positive buffers

The coordinate `t` increases from a cut towards the retained interval and is
measured in units of the inverse mass.  Both ends therefore have the same
buffer `[0, action + 6]`, with the exterior lying at negative coordinates.
This module extracts the geometric and potential estimates from the actual
R09 hypotheses; it does not assume a compressed inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

/-- Inward coordinate in units of one inverse mass. -/
def positiveBufferPoint (B : BufferData) (i : Fin 2) (t : ℝ) : ℝ :=
  bufferCut B i - bufferSign i * t / B.mass i

@[simp] theorem positiveBufferPoint_zero (B : BufferData) (i : Fin 2) :
    positiveBufferPoint B i 0 = bufferCut B i := by
  simp only [positiveBufferPoint, mul_zero, zero_div, sub_zero]

theorem positiveBufferPoint_innerWall (B : BufferData) (i : Fin 2) :
    positiveBufferPoint B i (B.action i + 6) = bufferInnerWall B i := rfl

theorem buffer_mass_pos {B : BufferData} (hB : BufferHypotheses B) (i : Fin 2) :
    0 < B.mass i := hB.2.2.2.2.2.2.2.2.2.2.1 i |>.1

theorem buffer_action_pos {B : BufferData} (hB : BufferHypotheses B) (i : Fin 2) :
    0 < B.action i := hB.2.2.2.2.2.2.2.2.2.2.1 i |>.2

theorem bufferSign_sq (i : Fin 2) : bufferSign i ^ 2 = 1 := by
  simp only [bufferSign]
  split_ifs <;> norm_num

theorem abs_bufferSign (i : Fin 2) : |bufferSign i| = 1 := by
  simp only [bufferSign]
  split_ifs <;> norm_num

theorem positiveBufferPoint_distance {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) (s t : ℝ) :
    |positiveBufferPoint B i s - positiveBufferPoint B i t| =
      |s - t| / B.mass i := by
  have hm := buffer_mass_pos hB i
  have he : positiveBufferPoint B i s - positiveBufferPoint B i t =
      -(bufferSign i * (s - t) / B.mass i) := by
    unfold positiveBufferPoint
    ring
  rw [he, abs_neg, abs_div, abs_mul, abs_bufferSign, one_mul, abs_of_pos hm]

theorem positiveBufferPoint_potential_lower {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {t : ℝ}
    (ht : t ≤ B.action i + 6) :
    B.mass i ^ 2 ≤ B.potential (positiveBufferPoint B i t) := by
  rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, hm, _, hlo, _, _⟩
  apply hlo i
  have hm' := (hm i).1
  have hdiv := (div_le_div_iff_of_pos_right hm').2 ht
  by_cases hi : i = 0
  · simp only [positiveBufferPoint, bufferCut, bufferSign, hi, if_true, neg_mul,
      one_mul, neg_div, sub_neg_eq_add]
    simpa only [hi, add_comm] using add_le_add_left hdiv B.l
  · simp only [positiveBufferPoint, bufferCut, bufferSign, hi, if_false, one_mul]
    exact sub_le_sub_left hdiv B.h

theorem positiveBufferPoint_potential_upper_cut {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {t : ℝ} (ht : |t| ≤ 4) :
    B.potential (positiveBufferPoint B i t) ≤ B.layerBound * B.mass i ^ 2 := by
  have hm := buffer_mass_pos hB i
  have hdist := positiveBufferPoint_distance hB i t 0
  rw [positiveBufferPoint_zero, sub_zero] at hdist
  rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hup, _⟩
  apply hup i
  exact Or.inl (hdist.le.trans ((div_le_div_iff_of_pos_right hm).2 ht))

theorem positiveBufferPoint_potential_upper_inner {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {t : ℝ}
    (ht : |t - (B.action i + 6)| ≤ 4) :
    B.potential (positiveBufferPoint B i t) ≤ B.layerBound * B.mass i ^ 2 := by
  have hm := buffer_mass_pos hB i
  have hdist := positiveBufferPoint_distance hB i t (B.action i + 6)
  rw [positiveBufferPoint_innerWall] at hdist
  rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hup, _⟩
  apply hup i
  exact Or.inr (hdist.le.trans ((div_le_div_iff_of_pos_right hm).2 ht))

/-- The compact scalar border vanishes throughout either buffer and its exterior. -/
theorem positiveBufferPoint_border_eq_zero {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {t : ℝ}
    (ht : t ≤ B.action i + 6) : B.borderFunction (positiveBufferPoint B i t) = 0 := by
  have hm := buffer_mass_pos hB i
  rcases hB with ⟨_, _, _, _, _, _, _, _, _, hsupp, _, _, _, _, _⟩
  by_contra hne
  have hx := hsupp hne
  have hdiv := (div_le_div_iff_of_pos_right hm).2 ht
  fin_cases i
  · have hleft := hx.1
    simp only [positiveBufferPoint, bufferInnerWall, bufferCut, bufferSign,
      Fin.zero_eta, if_true, neg_mul, one_mul, neg_div, sub_neg_eq_add] at hleft
    have hd : t / B.mass 0 ≤ (B.action 0 + 6) / B.mass 0 := by simpa only [] using hdiv
    linarith only [hleft, hd]
  · have hright := hx.2
    norm_num [positiveBufferPoint, bufferInnerWall, bufferCut, bufferSign] at hright
    have hd : t / B.mass 1 ≤ (B.action 1 + 6) / B.mass 1 := by simpa only [] using hdiv
    linarith only [hright, hd]

/-- A nonempty positive buffer necessarily has layer constant at least one. -/
theorem buffer_one_le_layerBound {B : BufferData} (hB : BufferHypotheses B) :
    1 ≤ B.layerBound := by
  have hm := buffer_mass_pos hB 0
  have ha := buffer_action_pos hB 0
  have hlo := positiveBufferPoint_potential_lower hB 0 (t := 0) (by linarith)
  have hup := positiveBufferPoint_potential_upper_cut hB 0 (t := 0) (by norm_num)
  nlinarith [sq_pos_of_pos hm]

end ContinuousFlexibility.Radial
