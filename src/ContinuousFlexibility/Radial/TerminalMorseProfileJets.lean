module

public import ContinuousFlexibility.Radial.TerminalMorsePhysicalJets

/-!
# Actual profile coefficients on the terminal cutoff layer

The profile and its first derivative are bounded by differentiating the
same weight identity w(Rt)=weightScale R'(t). The radius equation and
the actual Morse potential bounds control R''. The reciprocal Hilbert
density follows from the same positive speed floor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

theorem terminalMorse_retained_speed_upper {A B x : ℝ} {r : ℝ → ℝ}
    (hA : 0 < A) (hA₀ : A ≤ 1 / 1000) (hr : IsNormalizedMorseCell A B r)
    (hx : x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))) :
    deriv r x ≤ 7 * A := by
  by_cases ht : x ≤ morseRightTurn A B
  · exact (hr.left_half x ⟨hx.1, ht⟩).2.2.2.2
  · have hv := (hr.right_half x ⟨le_of_not_ge ht, hx.2⟩).2.2.2.2
    have hp : A ^ 4 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hA.le (hA₀.trans (by norm_num : (1 / 1000 : ℝ) ≤ 1)) 4
    have hpower : A ^ 5 ≤ A := by
      have h := mul_le_mul_of_nonneg_left hp hA.le
      nlinarith only [h]
    nlinarith only [hv, hpower, hA]

theorem terminalMorseLayer_rho_bounds (long : Bool) {A B t : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000) (hBA : B ≤ A ^ 9)
    (ht : t ∈ Icc 0 (terminalMorseLayerLength long A)) :
    0 ≤ -morseRho A B (terminalMorseLayerOrigin long A B + t) ∧
      -morseRho A B (terminalMorseLayerOrigin long A B + t) ≤ A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  cases long
  · change t ∈ Icc 0 morseShortLeftCapLength at ht
    have hx : morseCellLeftCut + t ∈ Icc morseCellLeftCut morseShortLeftCapCut := by
      dsimp only [morseShortLeftCapLength] at ht
      constructor <;> linarith only [ht.1, ht.2]
    exact ⟨(div_pos hA (by norm_num)).le.trans (morseShortLeftCap_negRho_lower hB hAB hx.2),
      morseLeftCap_negRho_upper hB hAB hx.1⟩
  · have hx : morseRightTurn A B ≤ morseRightTurn A B + t := le_add_of_nonneg_right ht.1
    have hq := morseRho_right_cap_bounds hB hAB hx
    exact ⟨hq.1, hq.2.trans (terminalMorse_B_le_A hA hA₀ hBA)⟩

theorem terminalMorseLayerRadius_equation (long : Bool) {A B s t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r)
    (ht : t ∈ Icc 0 (terminalMorseLayerLength long A)) :
    deriv (deriv (terminalMorseLayerRadius long A B s r)) t =
      -morseRho A B (terminalMorseLayerOrigin long A B + t) *
        terminalMorseLayerRadius long A B s r t := by
  cases long
  · exact (terminalMorse_short_cap_geometry (j := 0) hB hAB hs hr ht).2.2.1
  · exact (terminalMorse_long_cap_geometry (j := 0) hB hAB hs hr ht).2.2.1

/-- All coefficient estimates are obtained from the actual profile,
including the derivative and the inverse density needed by the source. -/
theorem terminalMorse_physical_layer_coefficients (long : Bool) {A B s weightScale z : ℝ}
    {r w : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hscale : 0 < weightScale)
    (hA₀ : A ≤ 1 / 1000) (hBA : B ≤ A ^ 9)
    (hr : IsNormalizedMorseCell A B r) (hw : ContDiff ℝ ∞ w)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hz : z ∈ Icc (terminalMorseLayerLeft long A B s r) (terminalMorseLayerRight long A B s r)) :
    0 < w z ∧ |w z| ≤ 7 * weightScale * s * A ∧
      |deriv w z| ≤ (2 * weightScale * s * A) / (s * A ^ 5 / 100) ∧
      |z ^ 2 / (12 * w z)| ≤ (2 * s) ^ 2 / (12 * (weightScale * (s * A ^ 5 / 100))) := by
  let R := terminalMorseLayerRadius long A B s r
  let L := terminalMorseLayerLength long A
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hR : ContDiff ℝ ∞ R := terminalMorseLayerRadius_smooth long A B s hr.smooth
  obtain ⟨t, ht, htz⟩ := terminalMorseLayer_preimage long hB hAB hs hr hz
  have htfull : t ∈ Icc 0 L := ⟨by linarith only [ht.1, hL], by linarith only [ht.2, hL]⟩
  have hx := terminalMorseLayer_point_mem long hB hAB htfull
  have hRp : 0 < R t := terminalMorseLayerRadius_pos long hB hAB hs hr htfull
  have hRupper : R t ≤ 2 * s := by
    have h := mul_le_mul_of_nonneg_left (terminalMorse_retained_radius_bounds hr hx).2 hs.le
    simpa only [R, terminalMorseLayerRadius, terminalMorseCapRadius, one_mul, mul_one, mul_comm] using h
  have hspeed : s * A ^ 5 / 100 ≤ deriv R t :=
    terminalMorseLayerRadius_speed_lower long hB hAB hs hr htfull
  have hspeedpos : 0 < deriv R t := (by positivity : 0 < s * A ^ 5 / 100).trans_le hspeed
  have hspeedupper : deriv R t ≤ 7 * s * A := by
    have h := mul_le_mul_of_nonneg_left (terminalMorse_retained_speed_upper hA hA₀ hr hx) hs.le
    change deriv (terminalMorseCapRadius s (terminalMorseLayerOrigin long A B) 1 r) t ≤ _
    rw [terminalMorseCapRadius_deriv _ _ _ _ hr.smooth]
    simp only [one_mul, mul_one]
    nlinarith only [h]
  have hweightR (x : ℝ) (hx : x ∈ Icc 0 L) : w (R x) = weightScale * deriv R x := by
    change w (s * r (terminalMorseLayerOrigin long A B + 1 * x)) =
      weightScale * deriv (terminalMorseCapRadius s (terminalMorseLayerOrigin long A B) 1 r) x
    rw [terminalMorseCapRadius_deriv _ _ _ _ hr.smooth]
    simpa only [one_mul, mul_one] using hweight _ (terminalMorseLayer_point_mem long hB hAB hx)
  have hwlower : weightScale * (s * A ^ 5 / 100) ≤ w (R t) := by
    rw [hweightR t htfull]
    exact mul_le_mul_of_nonneg_left hspeed hscale.le
  have hwpos : 0 < w (R t) := (by positivity : 0 < weightScale * (s * A ^ 5 / 100)).trans_le hwlower
  have hrho := terminalMorseLayer_rho_bounds long hB hAB hA₀ hBA htfull
  have heq : deriv (deriv R) t =
      -morseRho A B (terminalMorseLayerOrigin long A B + t) * R t :=
    terminalMorseLayerRadius_equation long hB hAB hs hr htfull
  have hdw := r07_cap_weight_derivative hL hR hw hweightR htfull
  rw [heq] at hdw
  have hderiv : deriv w (R t) =
      weightScale * (-morseRho A B (terminalMorseLayerOrigin long A B + t) * R t) / deriv R t :=
    (eq_div_iff hspeedpos.ne').mpr hdw
  have hnum : weightScale * (-morseRho A B (terminalMorseLayerOrigin long A B + t) * R t) ≤
      weightScale * (A * (2 * s)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hrho.2 hRupper hRp.le hA.le) hscale.le
  have hdwbound : |deriv w (R t)| ≤ (2 * weightScale * s * A) / (s * A ^ 5 / 100) := by
    rw [hderiv, abs_of_nonneg (div_nonneg (mul_nonneg hscale.le
      (mul_nonneg hrho.1 hRp.le)) hspeedpos.le)]
    calc
      _ ≤ (weightScale * (A * (2 * s))) / deriv R t :=
        div_le_div_of_nonneg_right hnum hspeedpos.le
      _ ≤ (weightScale * (A * (2 * s))) / (s * A ^ 5 / 100) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hspeed
      _ = _ := by ring
  rw [← htz]
  refine ⟨hwpos, ?_, hdwbound, ?_⟩
  · rw [abs_of_pos hwpos, hweightR t htfull]
    have h := mul_le_mul_of_nonneg_left hspeedupper hscale.le
    nlinarith only [h]
  · rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity : 0 ≤ 12 * w (R t)))]
    calc
      _ ≤ (2 * s) ^ 2 / (12 * w (R t)) :=
        div_le_div_of_nonneg_right ((sq_le_sq₀ hRp.le (by positivity)).mpr hRupper) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hwlower (by norm_num))

end ContinuousFlexibility.Radial
