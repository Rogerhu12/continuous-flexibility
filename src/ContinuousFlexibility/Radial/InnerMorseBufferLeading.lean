module

public import ContinuousFlexibility.Radial.InnerMorsePhysicalChart
public import ContinuousFlexibility.Radial.InnerMorseWeights

/-!
# The genuine Morse buffers and their physical leading scale

Both closed cut-to-wall intervals lie in the original retained positive
caps. The actual radius ODE therefore proves the velocity-to-mass bound
with one fixed constant. The interpolation between the two inner walls
has exactly the prescribed cut weight on either complete buffer.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem innerMorseBuffer_closedSpan_subset_cap {A B j : ℝ} (B₀ : ℝ)
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hsmall : A ≤ 1 / 10)
    (i : Fin 2) :
    uIcc (bufferCut (innerMorseBufferData A B j B₀) i)
      (bufferInnerWall (innerMorseBufferData A B j B₀) i) ⊆
        innerMorseCapInterval A B (decide (i ≠ 0)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hmass := innerMorseBufferMass_pos hB hAB hj
  have hshort := morseCellLeftCut_lt_shortLeftCapCut
  have hlong := innerMorseBuffer_long_fit hA hsmall
  have hL := morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · rw [innerMorseBufferInnerWall_zero B₀ (hmass 0).ne']
    simp only [bufferCut, innerMorseBufferData, ite_true, ne_eq, not_true_eq_false,
      decide_false, innerMorseCapInterval, Bool.false_eq_true, ite_false]
    apply uIcc_subset_Icc
    · dsimp only [innerMorseBufferLeftCut]
      exact ⟨by linarith only [hshort], by linarith only [hshort]⟩
    · exact ⟨hshort.le, le_rfl⟩
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [innerMorseBufferInnerWall_one B₀ (hmass 1).ne']
    simp only [bufferCut, innerMorseBufferData, h10, ite_false,
      decide_true, innerMorseCapInterval, ite_true]
    apply uIcc_subset_Icc
    · dsimp only [innerMorseBufferRightCut, morseRightCapEnd]
      exact ⟨by linarith only [hlong, hL], by linarith only [hL]⟩
    · dsimp only [morseRightCapEnd]
      exact ⟨by linarith only [hlong], by linarith only [hL]⟩

/-- No supplied cap-velocity bound is needed: this is the actual
realized radius and the actual mass at either model endpoint. -/
theorem innerMorseChain_buffer_cap_ratio {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {cost : ℕ → ℝ} (h : MorseChainRealization T σ D cost)
    (side : Bool) {m : ℕ} (hindex : 10 ≤ T.index) (hm : T.index ≤ m)
    {j : ℝ} (hj : 0 < j) (B₀ : ℝ) (i : Fin 2) {x : ℝ}
    (hx : x ∈ uIcc
      (bufferCut (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀) i)
      (bufferInnerWall (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀) i)) :
    |deriv (T.radius side m) x / T.radius side m x| /
      innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i ≤ 30000 / j := by
  obtain ⟨hB, hAB, _, hlt, hgt, _, hspeed⟩ := h.retained_data side m hm
  obtain ⟨hl, hr⟩ := innerMorseChain_retained_endpoints h side hm
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
  have hcap := innerMorseBuffer_closedSpan_subset_cap B₀ hB hAB hj
    (innerMorseChain_parameter_small h hindex hm) i hx
  simpa only [innerMorseBufferMass] using
    innerMorse_cap_upsilon_over_mass hB hAB (innerMorseChain_parameter_tiny h hindex hm)
      hBA.1 hBA.2 hs (h.radius_smooth side m hm) rfl hspeed hEq hj (decide (i ≠ 0)) hcap

/-- The entire physical cut interval lies in the core, as follows from
the endpoints of the original actual realization. -/
theorem innerMorseChain_buffer_in_core {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {cost : ℕ → ℝ} (h : MorseChainRealization T σ D cost)
    (side : Bool) {m : ℕ} (hm : T.index ≤ m) :
    Ioo (T.radius side m innerMorseBufferLeftCut)
      (T.radius side m (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))) ⊆
        radialCore D := by
  have hc := (innerMorseChainCut_geometry h side hm).2.2.2
  have hl : D.a < T.radius side m innerMorseBufferLeftCut := by
    have h0 := hc 0
    simpa only [innerMorseChainCut_zero, radialCore, mem_Ioo] using h0.1
  have hr : T.radius side m (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m)) < D.b := by
    have h1 := hc 1
    simpa only [innerMorseChainCut_one, radialCore, mem_Ioo] using h1.2
  intro r hrange
  exact ⟨hl.trans hrange.1, hrange.2.trans hr⟩

/-- Interpolating only between the two inner walls leaves every buffer
at its own geometric-mean cut value. Both endpoints use one statement. -/
theorem innerMorseInterpolatedWeight_on_buffer {B : BufferData} (hB : BufferHypotheses B)
    (N : ℕ) (a γ : ℝ) (side : Bool) (m : ℕ) (i : Fin 2) {x : ℝ}
    (hx : x ∈ uIcc (bufferCut B i) (bufferInnerWall B i)) :
    innerMorseInterpolatedWeight N a γ side m
      (bufferInnerWall B 0) (bufferInnerWall B 1) x = innerMorseCutWeight N a γ side m i := by
  have hw := innerBuffer_walls_inside hB
  have hleft := innerMorseCutWeight_pos N a γ side m 0
  have hright := innerMorseCutWeight_pos N a γ side m 1
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · have hx0 : x ∈ Icc B.l (bufferInnerWall B 0) := by
      simpa only [bufferCut, ite_true, uIcc_of_le hw.1.le] using hx
    have hx' : x ≤ bufferInnerWall B 0 := hx0.2
    simpa only [innerMorseInterpolatedWeight, Bool.false_eq_true, ite_false] using
      innerInterpolatedWeight_eqOn_buffer hw.2.1 hleft hright false hx'
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hx1 : x ∈ Icc (bufferInnerWall B 1) B.h := by
      simpa only [bufferCut, h10, ite_false, uIcc_of_ge hw.2.2.le] using hx
    have hx' : bufferInnerWall B 1 ≤ x := hx1.1
    simpa only [innerMorseInterpolatedWeight, ite_true] using
      innerInterpolatedWeight_eqOn_buffer hw.2.1 hleft hright true hx'

end ContinuousFlexibility.Radial
