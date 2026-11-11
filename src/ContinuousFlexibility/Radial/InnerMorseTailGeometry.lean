import ContinuousFlexibility.Radial.InnerMorseBufferVelocity
import ContinuousFlexibility.Radial.InnerPositiveGapGeometry

/-!
# Actual cut geometry and positive caps of both Morse tails

The two cuts are those of the actual Morse BufferData. Their physical
ordering follows from the original increasing radius, on either tail.
The already proved velocity-to-mass estimate gives one fixed lower
bound for the physical logarithmic slope on both outer caps. Neither a
frequency, a tail truncation nor a local inverse enters this bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- A common positive slope for all retained outer Morse caps. -/
def innerMorseTailSlope : ℝ := 1 / (30000 : ℝ) ^ 2

theorem innerMorseTailSlope_pos : 0 < innerMorseTailSlope := by
  norm_num [innerMorseTailSlope]

theorem innerMorseTailSlope_le_two : innerMorseTailSlope ≤ 2 := by
  norm_num [innerMorseTailSlope]

/-- The actual physical cut; its location is independent of frequency. -/
def innerMorseChainCut (T : MorseChainData) (side : Bool) (m : ℕ) (i : Fin 2) : ℝ :=
  T.radius side m (if i = 0 then innerMorseBufferLeftCut
    else innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))

@[simp] theorem innerMorseChainCut_zero (T : MorseChainData) (side : Bool) (m : ℕ) :
    innerMorseChainCut T side m 0 = T.radius side m innerMorseBufferLeftCut := by
  simp only [innerMorseChainCut, ite_true]

@[simp] theorem innerMorseChainCut_one (T : MorseChainData) (side : Bool) (m : ℕ) :
    innerMorseChainCut T side m 1 = T.radius side m
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m)) := by
  simp only [innerMorseChainCut, show (1 : Fin 2) ≠ 0 by decide, ite_false]

theorem innerMorseChainCut_eq_bufferCut (T : MorseChainData) (side : Bool) (m : ℕ)
    (j B₀ : ℝ) (i : Fin 2) :
    innerMorseChainCut T side m i = T.radius side m
      (bufferCut (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀) i) := by
  simp only [innerMorseChainCut, bufferCut, innerMorseBufferData]

theorem innerMorseBuffer_cut_order {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    morseCellLeftCut < innerMorseBufferLeftCut ∧
      innerMorseBufferLeftCut < innerMorseBufferRightCut A B ∧
      innerMorseBufferRightCut A B < morseRightCapEnd A B (1 / 100) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hshort := morseCellLeftCut_lt_shortLeftCapCut
  have hturn := (morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)
  have hlong := morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)
  dsimp only [innerMorseBufferLeftCut, innerMorseBufferRightCut, morseRightCapEnd]
  exact ⟨by linarith only [hshort], by linarith only [hshort, hturn, hlong],
    by linarith only [hlong]⟩

theorem innerMorseChain_retained_endpoints {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {m : ℕ} (hm : T.index ≤ m) :
    T.leftX side m = morseCellLeftCut ∧
      T.rightX side m = morseRightCapEnd (morseChainA T m) (morseChainB T m) (1 / 100) := by
  obtain ⟨_, _, hl, _, _, hr, _⟩ := h.retained_data side m hm
  refine ⟨hl, ?_⟩
  simpa only [morseChainRightTurn, morseRightTurn, morseRightRootT,
    morseRightCapEnd, morseRightCapLength] using hr

/-- The cut model is strictly inside its original retained cell, and
both cuts belong to the actual radial core. -/
theorem innerMorseChainCut_geometry {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {m : ℕ} (hm : T.index ≤ m) :
    T.radius side m (T.leftX side m) < innerMorseChainCut T side m 0 ∧
      innerMorseChainCut T side m 0 < innerMorseChainCut T side m 1 ∧
      innerMorseChainCut T side m 1 < T.radius side m (T.rightX side m) ∧
      ∀ i, innerMorseChainCut T side m i ∈ radialCore D := by
  obtain ⟨hB, hAB, _, _, _, _, _⟩ := h.retained_data side m hm
  obtain ⟨hl, hr⟩ := innerMorseChain_retained_endpoints h side hm
  obtain ⟨h0, h01, h1⟩ := innerMorseBuffer_cut_order hB hAB
  have h0' : T.leftX side m < innerMorseBufferLeftCut := by simpa only [hl] using h0
  have h1' : innerMorseBufferRightCut (morseChainA T m) (morseChainB T m) <
      T.rightX side m := by simpa only [hr] using h1
  have hab : T.leftX side m ≤ T.rightX side m := (h0'.trans (h01.trans h1')).le
  have hc0 : innerMorseBufferLeftCut ∈ Icc (T.leftX side m) (T.rightX side m) :=
    ⟨h0'.le, (h01.trans h1').le⟩
  have hc1 : innerMorseBufferRightCut (morseChainA T m) (morseChainB T m) ∈
      Icc (T.leftX side m) (T.rightX side m) := ⟨(h0'.trans h01).le, h1'.le⟩
  have hmR := h.radius_strictMonoOn side m hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [innerMorseChainCut_zero]
    exact hmR (left_mem_Icc.mpr hab) hc0 h0'
  · rw [innerMorseChainCut_zero, innerMorseChainCut_one]
    exact hmR hc0 hc1 h01
  · rw [innerMorseChainCut_one]
    exact hmR hc1 (right_mem_Icc.mpr hab) h1'
  · intro i
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [innerMorseChainCut_zero]
      exact h.radius_mem_core side m hm _ hc0
    · rw [innerMorseChainCut_one]
      exact h.radius_mem_core side m hm _ hc1

theorem innerMorseCapInterval_subset {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (right : Bool) : innerMorseCapInterval A B right ⊆
      Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hshort := (morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)
  have hturn := morseCellLeftCut_lt_rightTurn hB hAB
  have hlong := morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)
  have hlog := log_pos (by norm_num : (1 : ℝ) < 4)
  intro x hx
  cases right with
  | false =>
    simp only [innerMorseCapInterval, Bool.false_eq_true, ite_false] at hx
    exact ⟨hx.1, hx.2.trans (hshort.le.trans (le_add_of_nonneg_right hlong.le))⟩
  | true =>
    simp only [innerMorseCapInterval, ite_true] at hx
    exact ⟨by linarith only [hx.1, hlog, hturn], hx.2⟩

/-- The slope is obtained from the actual profile/radius identity and
the already proved cap mass estimate, with the auxiliary frequency one.
This proves a fixed geometric bound for every later physical frequency. -/
theorem innerMorseChain_cap_logSlope {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {m : ℕ} (hindex : 10 ≤ T.index) (hm : T.index ≤ m)
    (right : Bool) {x : ℝ}
    (hx : x ∈ innerMorseCapInterval (morseChainA T m) (morseChainB T m) right) :
    innerMorseTailSlope ≤
      T.radius side m x * deriv D.w (T.radius side m x) / D.w (T.radius side m x) := by
  obtain ⟨hB, hAB, _, hlt, hgt, _, hspeed⟩ := h.retained_data side m hm
  obtain ⟨hl, hr⟩ := innerMorseChain_retained_endpoints h side hm
  have hxwhole : x ∈ Icc (T.leftX side m) (T.rightX side m) := by
    simpa only [hl, hr] using innerMorseCapInterval_subset hB hAB right hx
  have hs : 0 < T.radius side m (morseChainRightTurn T m) :=
    h.radius_positive side m hm _ ⟨hlt.le, hgt.le⟩
  have hd1 : (1 : ℝ) ≤ T.d m := by
    rw [h.d_eq m hm]
    exact_mod_cast (show 1 ≤ morseChainInteger m from
      (by decide : 1 ≤ 2).trans (morseChainInteger_ge_two m))
  have hBA := morseChainB_A_bounds T m hd1
  have hEq : ∀ y ∈ Icc morseCellLeftCut
      (morseRightCapEnd (morseChainA T m) (morseChainB T m) (1 / 100)),
      deriv (deriv (T.radius side m)) y =
        -morseRho (morseChainA T m) (morseChainB T m) y * T.radius side m y := by
    intro y hy
    apply h.equation side m hm y
    simpa only [hl, hr] using hy
  have hmass := innerMorseCapMass_spec hB hAB (by norm_num : (0 : ℝ) < 1) right hx
  have hratio := innerMorse_cap_upsilon_over_mass hB hAB
    (innerMorseChain_parameter_tiny h hindex hm) hBA.1 hBA.2 hs
    (h.radius_smooth side m hm) rfl hspeed hEq (by norm_num : (0 : ℝ) < 1) right hx
  norm_num only [div_one] at hratio
  have hbound := (div_le_iff₀ hmass.1).mp hratio
  have hsq := (sq_le_sq₀ (abs_nonneg (deriv (T.radius side m) x / T.radius side m x))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 30000) hmass.1.le)).mpr hbound
  simp only [sq_abs, mul_pow] at hsq
  have hmass' : innerMorseCapMass (morseChainA T m) (morseChainB T m) 1 right ^ 2 ≤
      -morseRho (morseChainA T m) (morseChainB T m) x := by
    simpa only [one_pow, one_mul] using hmass.2
  have hquad := hsq.trans (mul_le_mul_of_nonneg_left hmass'
    (sq_nonneg (30000 : ℝ)))
  have hRp := h.radius_positive side m hm x hxwhole
  have hvp := h.derivative_positive side m hm x hxwhole
  have hlam : morseChainAmplitude T σ m ≠ 0 := by
    intro hz
    have hwx := h.geometry.2.2.2.2.1 _ (h.radius_mem_core side m hm x hxwhole)
    apply hwx.ne'
    rw [h.profile_eq side m hm x hxwhole, hz, zero_mul]
  have hid := innerProfile_logSlope_identity (rho := morseRho (morseChainA T m) (morseChainB T m))
    (hlt.trans hgt) (h.radius_smooth side m hm) h.geometry.2.2.1.1
    hlam hRp.ne' hvp.ne' (h.profile_eq side m hm) (h.equation side m hm x hxwhole) hxwhole
  unfold innerMorseTailSlope
  apply (mul_le_mul_right (sq_pos_of_pos (div_pos hvp hRp))).mp
  rw [hid]
  nlinarith only [hquad]

end ContinuousFlexibility.Radial
