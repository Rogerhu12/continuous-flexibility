import ContinuousFlexibility.Radial.TerminalMorseShortCap

/-!
# The actual positive portion and cutoff window of a long Morse cap

The potential is nonnegative from the turning point onward. A positive
mass lower bound is used only after the fixed offset log 4. The actual
relations between A and B give an absolute action bound on a fixed
fraction of the long cap, including a complete derivative window.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

/-- Full-cap geometry, with the positive mass estimate explicitly
restricted to points beyond the turning-point collar. -/
theorem terminalMorse_long_cap_geometry {A B j s t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r)
    (ht : t ∈ Icc 0 (morseRightCapLength A (1 / 100))) :
    let R := terminalMorseCapRadius s (morseRightTurn A B) 1 r
    0 < R t ∧ 0 < deriv R t ∧
      deriv (deriv R) t = -morseRho A B (morseRightTurn A B + t) * R t ∧
      0 ≤ j ^ 2 * (-morseRho A B (morseRightTurn A B + t)) ∧
      j ^ 2 * (-morseRho A B (morseRightTurn A B + t)) ≤ (j * sqrt B) ^ 2 ∧
      (log 4 ≤ t →
        (j * sqrt B / 2) ^ 2 ≤ j ^ 2 * (-morseRho A B (morseRightTurn A B + t))) := by
  dsimp only
  have hx : morseRightTurn A B + t ∈
      Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)) := by
    constructor
    · linarith only [ht.1]
    · dsimp only [morseRightCapEnd]
      linarith only [ht.2]
  have hleft := morseCellLeftCut_lt_rightTurn hB hAB
  have hcollar : (0 : ℝ) ≤ morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
  have hxwide : morseRightTurn A B + t ∈ Icc (morseCellLeftCut - morseJoinCollarWidth)
      (morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth) :=
    ⟨by linarith only [hx.1, hleft, hcollar], by linarith only [hx.2, hcollar]⟩
  have hp := (hr.right_half _ hx).2.1
  have hv := hr.speed_pos _ hxwide
  have hq := morseRho_right_cap_bounds hB hAB hx.1
  refine ⟨?_, ?_, ?_, mul_nonneg (sq_nonneg _) hq.1, ?_, ?_⟩
  · simpa only [terminalMorseCapRadius, one_mul] using mul_pos hs hp
  · rw [terminalMorseCapRadius_deriv s (morseRightTurn A B) 1 t hr.smooth]
    simpa only [one_mul, mul_one] using mul_pos hs hv
  · rw [terminalMorseCapRadius_second s (morseRightTurn A B) 1 t hr.smooth (by norm_num)]
    simp only [one_mul, terminalMorseCapRadius]
    rw [hr.equation _ hxwide]
    ring
  · rw [mul_pow, sq_sqrt hB.le]
    exact mul_le_mul_of_nonneg_left hq.2 (sq_nonneg j)
  · intro htfar
    have hfar : morseRightTurn A B + log 4 ≤ morseRightTurn A B + t := by
      linarith only [htfar]
    have hlo := morseRho_right_cap_lower hB hAB hfar
    have hmul := mul_le_mul_of_nonneg_left hlo (sq_nonneg j)
    rw [div_pow, mul_pow, sq_sqrt hB.le]
    norm_num
    nlinarith only [hmul, mul_nonneg (sq_nonneg j) hB.le]

/-- The actual B-to-A relation controls the long-cap mass times length.
The deliberately coarse constant is absolute. -/
theorem terminalMorse_long_action_lower {A B j : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hj : 0 < j)
    (hBA : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) :
    j * sqrt A / 11809800 ≤
      (j * sqrt B / 2) * morseRightCapLength A (1 / 100) := by
  have hsqrt : A ^ 4 * sqrt A / 59049 ≤ sqrt B := by
    apply (sq_le_sq₀ (by positivity) (sqrt_nonneg B)).mp
    rw [sq_sqrt hB.le]
    calc
      (A ^ 4 * sqrt A / 59049) ^ 2 = A ^ 9 / (59049 : ℝ) ^ 2 := by
        rw [div_pow, mul_pow, sq_sqrt hA.le]
        ring
      _ ≤ A ^ 9 / (9 : ℝ) ^ 9 :=
        div_le_div_of_nonneg_left (pow_nonneg hA.le 9) (by norm_num) (by norm_num)
      _ ≤ B := hBA
  have hbase : (j * sqrt A) * A ^ 4 ≤ 59049 * j * sqrt B := by
    have h := mul_le_mul_of_nonneg_left hsqrt hj.le
    nlinarith only [h]
  have hbudget : j * sqrt A ≤
      11809800 * ((j * sqrt B / 2) * morseRightCapLength A (1 / 100)) := by
    calc
      _ ≤ (59049 * j * sqrt B) / A ^ 4 := (le_div_iff₀ (pow_pos hA 4)).mpr hbase
      _ = _ := by dsimp only [morseRightCapLength]; ring
  nlinarith only [hbudget]

/-- The retained long cap is much longer than its fixed turning-point
collar for every actual small Morse parameter. -/
theorem terminalMorse_long_length_lower {A : ℝ} (hA : 0 < A) (hA₀ : A ≤ 1 / 1000) :
    (100 : ℝ) ≤ morseRightCapLength A (1 / 100) := by
  have hp := pow_le_pow_left₀ hA.le
    (hA₀.trans (by norm_num : (1 / 1000 : ℝ) ≤ 1 / 10)) 4
  norm_num at hp
  unfold morseRightCapLength
  apply (le_div_iff₀ (pow_pos hA 4)).mpr
  nlinarith only [hp]

/-- A fixed middle-quarter layer lies beyond the turning point collar.
Its complete forward derivative window leaves one quarter of the cap
between the window and the normalized outer endpoint. -/
theorem terminalMorse_long_layer_window {A B j t : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hj : 0 < j) (hA₀ : A ≤ 1 / 1000)
    (hBA : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (haction : 1000000000 ≤ j * sqrt A)
    (ht : t ∈ Icc (morseRightCapLength A (1 / 100) / 4)
      (morseRightCapLength A (1 / 100) / 2)) :
    0 < j * sqrt B / 2 ∧ log 4 ≤ t ∧
      t + 1 / (j * sqrt B / 2) ≤ 3 * morseRightCapLength A (1 / 100) / 4 ∧
      j * sqrt A / 50000000 ≤
        (j * sqrt B / 2) * (morseRightCapLength A (1 / 100) / 4) := by
  have hm : 0 < j * sqrt B / 2 := div_pos (mul_pos hj (sqrt_pos.mpr hB)) (by norm_num)
  have hlength := terminalMorse_long_length_lower hA hA₀
  have hmass := terminalMorse_long_action_lower hA hB hj hBA
  have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hwindow : 1 / (j * sqrt B / 2) ≤ morseRightCapLength A (1 / 100) / 4 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith only [hmass, haction]
  have haction₀ : 0 ≤ j * sqrt A := (mul_pos hj (sqrt_pos.mpr hA)).le
  exact ⟨hm, by linarith only [hlog, hlength, ht.1],
    by linarith only [ht.2, hwindow],
    by nlinarith only [hmass, haction₀]⟩

end ContinuousFlexibility.Radial
