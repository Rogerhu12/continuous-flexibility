import ContinuousFlexibility.Radial.InnerMorseBufferCoefficients

/-!
# The actual Morse radius on the retained cut models

The cuts used in BufferData lie inside the original realized cell.
The left and right radius ODE estimates give one fixed physical
velocity bound on that entire cut interval. The argument applies to
both tails with their original increasing model coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem innerMorseBufferInterval_subset {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    Icc innerMorseBufferLeftCut (innerMorseBufferRightCut A B) ⊆
      Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hleft : morseCellLeftCut ≤ innerMorseBufferLeftCut := by
    have h := morseCellLeftCut_lt_shortLeftCapCut
    unfold innerMorseBufferLeftCut
    linarith only [h]
  have hright : innerMorseBufferRightCut A B ≤ morseRightCapEnd A B (1 / 100) := by
    have h := morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)
    dsimp only [innerMorseBufferRightCut, morseRightCapEnd]
    linarith only [h]
  exact Icc_subset_Icc hleft hright

/-- The index ten already gives the smallness required by the actual
radius ODE estimates; no new choice after realization is required. -/
theorem innerMorseChain_parameter_tiny {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {m : ℕ} (hindex : 10 ≤ T.index) (hm : T.index ≤ m) :
    morseChainA T m ≤ 1 / 1000 := by
  have hm10 : (10 : ℝ) ≤ m := by exact_mod_cast hindex.trans hm
  have hlog10 : log (10 : ℝ) ≤ 9 := by
    simpa only [show (10 : ℝ) - 1 = 9 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
  have hlog : log (9000 : ℝ) ≤ 36 := by
    calc
      log (9000 : ℝ) ≤ log ((10 : ℝ) ^ 4) :=
        log_le_log (by norm_num) (by norm_num)
      _ = 4 * log (10 : ℝ) := by rw [log_pow]; norm_num
      _ ≤ 36 := by linarith only [hlog10]
  apply morseChainA_le_of_sq_ge_log T m (h.d_eq m hm) (by norm_num : (0 : ℝ) < 1 / 1000)
  norm_num only
  nlinarith only [hlog, hm10, sq_nonneg ((m : ℝ) - 10)]

/-- The same radius and speed normalization controls both cap sides
and the oscillatory middle of the cut Morse model. -/
theorem innerMorseBuffer_velocity {A B s : ℝ} {R : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9)
    (hs : 0 < s) (hR : ContDiff ℝ ∞ R)
    (hroot : R (morseRightTurn A B) = s)
    (hspeed : deriv R (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 * s)
    (hEq : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      deriv (deriv R) x = -morseRho A B x * R x)
    {x : ℝ} (hx : x ∈ Icc innerMorseBufferLeftCut (innerMorseBufferRightCut A B)) :
    |deriv R x / R x| ≤ 14 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hA1 : A ≤ 1 := hA₀.trans (by norm_num)
  have hwhole := innerMorseBufferInterval_subset hB hAB hx
  by_cases hturn : x ≤ morseRightTurn A B
  · have hυ : |deriv R x / R x| ≤ 14 * A := by
      simpa only [Bool.false_eq_true, ite_false] using
        innerMorse_upsilon_bounds hB hAB hA₀ hBAlo hBAhi hs hR hroot hspeed hEq false
          (show x ∈ Icc morseCellLeftCut (morseRightTurn A B) from ⟨hwhole.1, hturn⟩)
    exact hυ.trans (by nlinarith only [hA1])
  · have hυ : |deriv R x / R x| ≤ (3 / 50 : ℝ) * A ^ 5 := by
      simpa only [ite_true] using
        innerMorse_upsilon_bounds hB hAB hA₀ hBAlo hBAhi hs hR hroot hspeed hEq true
          (show x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)) from
            ⟨(lt_of_not_ge hturn).le, hwhole.2⟩)
    have hpow : A ^ 5 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hA.le hA1 5
    exact hυ.trans (by nlinarith only [hpow])

/-- This bound uses the actual realized radius on either tail, with
no supplied velocity envelope and no reflected coordinate. -/
theorem innerMorseChain_buffer_velocity {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) {m : ℕ} (hindex : 10 ≤ T.index) (hm : T.index ≤ m)
    {x : ℝ} (hx : x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))) :
    |deriv (T.radius side m) x / T.radius side m x| ≤ 14 := by
  obtain ⟨hB, hAB, hl, hlt, hgt, hr, hspeed⟩ := h.retained_data side m hm
  have hl' : T.leftX side m = morseCellLeftCut := hl
  have hr' : T.rightX side m =
      morseRightCapEnd (morseChainA T m) (morseChainB T m) (1 / 100) := by
    simpa only [morseChainRightTurn, morseRightTurn, morseRightRootT,
      morseRightCapEnd, morseRightCapLength] using hr
  have hs : 0 < T.radius side m (morseChainRightTurn T m) :=
    h.radius_positive side m hm _ ⟨hlt.le, hgt.le⟩
  have hd1 : (1 : ℝ) ≤ T.d m := by
    rw [h.d_eq m hm]
    exact_mod_cast (show 1 ≤ morseChainInteger m from
      (by decide : 1 ≤ 2).trans (morseChainInteger_ge_two m))
  have hBA := morseChainB_A_bounds T m hd1
  apply innerMorseBuffer_velocity hB hAB (innerMorseChain_parameter_tiny h hindex hm)
    hBA.1 hBA.2 hs (h.radius_smooth side m hm) rfl hspeed ?_ hx
  intro y hy
  apply h.equation side m hm y
  simpa only [hl', hr'] using hy

end ContinuousFlexibility.Radial
