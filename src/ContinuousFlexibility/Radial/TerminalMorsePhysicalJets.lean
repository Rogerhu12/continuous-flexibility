import ContinuousFlexibility.Radial.TerminalMorseCutoffGeometry
import ContinuousFlexibility.Radial.TerminalMorseLongCap

/-!
# Uniform physical jets on the constructed Morse cutoff layer

The short and long cap estimates are transported to every point of the
actual physical layer. The lower speed of the same normalized radius
removes the point-dependent denominator in the physical derivative.
Both orientations then use one absolute decay rate and one coefficient
budget.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

theorem terminalMorse_B_le_A {A B : ℝ} (hA : 0 < A) (hA₀ : A ≤ 1 / 1000)
    (hBA : B ≤ A ^ 9) : B ≤ A := by
  have hA1 : A ≤ 1 := hA₀.trans (by norm_num)
  have hp : A ^ 8 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hA.le hA1 8
  calc
    B ≤ A ^ 9 := hBA
    _ = A * A ^ 8 := by ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hp hA.le
    _ = A := mul_one _

theorem terminalMorse_physical_layer_jets (long : Bool) {A B j s weightScale z : ℝ}
    {r w u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hs : 0 < s) (hscale : weightScale ≠ 0)
    (hA₀ : A ≤ 1 / 1000) (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9)
    (hr : IsNormalizedMorseCell A B r) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hode : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      radialJacobi (j ^ 2) w u (s * r x) = 0)
    (hzero : u (s * r (if long then morseRightTurn A B else morseShortLeftCapCut)) = 0)
    (hjoin : u (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) = 1)
    (hinit : long = true → 0 < deriv u (s * r (morseRightTurn A B)))
    (haction : 1000000000 ≤ j * sqrt A)
    (hz : z ∈ Icc (terminalMorseLayerLeft long A B s r) (terminalMorseLayerRight long A B s r)) :
    |u z| ≤ 2 * exp (-(j * sqrt A / 50000000)) ∧
      |deriv u z| ≤ (600 * j * sqrt A / (s * A ^ 5)) * exp (-(j * sqrt A / 50000000)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have htau : 0 < j * sqrt A := mul_pos hj (sqrt_pos.mpr hA)
  have hBAless := terminalMorse_B_le_A hA hA₀ hBAhi
  have hsqrt : sqrt B ≤ sqrt A := sqrt_le_sqrt hBAless
  have hL := terminalMorseLayerLength_pos long hA
  obtain ⟨t, ht, htz⟩ := terminalMorseLayer_preimage long hB hAB hs hr hz
  have htfull : t ∈ Icc 0 (terminalMorseLayerLength long A) :=
    ⟨by linarith only [ht.1, hL], by linarith only [ht.2, hL]⟩
  have hdenlower : s * A ^ 5 / 100 ≤
      s * deriv r (terminalMorseLayerOrigin long A B + t) := by
    have h := terminalMorseLayerRadius_speed_lower long hB hAB hs hr htfull
    change s * A ^ 5 / 100 ≤ deriv (terminalMorseCapRadius s
      (terminalMorseLayerOrigin long A B) 1 r) t at h
    rw [terminalMorseCapRadius_deriv _ _ _ _ hr.smooth] at h
    simpa only [one_mul, mul_one] using h
  have hden : 0 < s * deriv r (terminalMorseLayerOrigin long A B + t) :=
    (by positivity : 0 < s * A ^ 5 / 100).trans_le hdenlower
  have hfrac (N : ℝ) (hN : N ≤ 6 * j * sqrt A) :
      N / (s * deriv r (terminalMorseLayerOrigin long A B + t)) ≤
        600 * j * sqrt A / (s * A ^ 5) := by
    calc
      _ ≤ (6 * j * sqrt A) / (s * deriv r (terminalMorseLayerOrigin long A B + t)) :=
        div_le_div_of_nonneg_right hN hden.le
      _ ≤ (6 * j * sqrt A) / (s * A ^ 5 / 100) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdenlower
      _ = _ := by field_simp [hs.ne', hA.ne'] <;> ring
  have hturn := morseCellLeftCut_lt_rightTurn hB hAB
  have hshort : morseShortLeftCapCut < morseRightTurn A B :=
    (morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)
  have hend : morseRightTurn A B ≤ morseRightCapEnd A B (1 / 100) :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hsubshort : Icc morseCellLeftCut morseShortLeftCapCut ⊆
      Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) :=
    Icc_subset_Icc le_rfl (hshort.le.trans hend)
  have hsublong : Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)) ⊆
      Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) :=
    Icc_subset_Icc hturn.le le_rfl
  rw [← htz]
  cases long
  · change t ∈ Icc (morseShortLeftCapLength / 4) (morseShortLeftCapLength / 2) at ht
    have hjet := terminalMorse_short_cap_layer_bounds hB hAB hj hs hscale hr hw hu
      (fun x hx => hweight x (hsubshort hx)) (fun x hx => hode x (hsubshort hx))
      hjoin hzero ((by norm_num : (1000 : ℝ) ≤ 1000000000).trans haction) ht
    have hexp : exp (-(j * sqrt A / 48)) ≤ exp (-(j * sqrt A / 50000000)) := by
      apply exp_le_exp.mpr
      nlinarith only [htau.le]
    have hv : |u (s * r (morseCellLeftCut + t))| ≤ 2 * exp (-(j * sqrt A / 50000000)) :=
      hjet.1.trans (by nlinarith only [hexp, exp_pos (-(j * sqrt A / 50000000))])
    have hd : |deriv u (s * r (morseCellLeftCut + t))| ≤
        (600 * j * sqrt A / (s * A ^ 5)) * exp (-(j * sqrt A / 50000000)) := by
      refine hjet.2.trans ?_
      exact mul_le_mul (hfrac _ (by nlinarith only [htau.le])) hexp (exp_pos _).le (by positivity)
    exact ⟨by simpa only [terminalMorseLayerRadius, terminalMorseLayerOrigin,
      terminalMorseCapRadius, Bool.false_eq_true, if_false, one_mul] using hv,
      by simpa only [terminalMorseLayerRadius, terminalMorseLayerOrigin,
        terminalMorseCapRadius, Bool.false_eq_true, if_false, one_mul] using hd⟩
  · change t ∈ Icc (morseRightCapLength A (1 / 100) / 4)
      (morseRightCapLength A (1 / 100) / 2) at ht
    have hjet := terminalMorse_long_cap_layer_bounds hB hAB hj hs hscale hA₀ hBAlo hr hw hu
      (fun x hx => hweight x (hsublong hx)) (fun x hx => hode x (hsublong hx))
      hzero (hinit rfl) hjoin haction ht
    have hd : |deriv u (s * r (morseRightTurn A B + t))| ≤
        (600 * j * sqrt A / (s * A ^ 5)) * exp (-(j * sqrt A / 50000000)) := by
      refine hjet.2.trans ?_
      exact mul_le_mul_of_nonneg_right
        (hfrac _ (mul_le_mul_of_nonneg_left hsqrt (by positivity))) (exp_pos _).le
    exact ⟨by simpa only [terminalMorseLayerRadius, terminalMorseLayerOrigin,
      terminalMorseCapRadius, if_true, one_mul] using hjet.1,
      by simpa only [terminalMorseLayerRadius, terminalMorseLayerOrigin,
        terminalMorseCapRadius, if_true, one_mul] using hd⟩

end ContinuousFlexibility.Radial
