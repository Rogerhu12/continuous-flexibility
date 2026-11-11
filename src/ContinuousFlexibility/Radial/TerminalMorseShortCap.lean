import ContinuousFlexibility.Radial.TerminalCapAttenuation
import ContinuousFlexibility.Radial.R07CapPullback
import ContinuousFlexibility.Radial.MorseChainGeometry

/-!
# Actual Morse short-cap attenuation

The radius is the same dilated normalized Morse radius used by the
incoming construction. Its physical homogeneous solution has value one
at the cell end and zero at the short-cap cut. The profile identity
therefore gives an actual scalar equation with coefficient -j² rho.

The cutoff layer occupies the middle quarter of the short cap. The
frequency hypothesis proves that the entire derivative window remains
inside that cap. Both physical jets then decay by exp (-j sqrt A / 48).
No scalar equation, potential bound, or exponential estimate is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

/-- An affine model coordinate, allowing either orientation. -/
def terminalMorseCapRadius (s origin direction : ℝ) (r : ℝ → ℝ) : ℝ → ℝ :=
  fun t => s * r (origin + direction * t)

theorem terminalMorseCapRadius_smooth (s origin direction : ℝ) {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (terminalMorseCapRadius s origin direction r) :=
  contDiff_const.mul (hr.comp (contDiff_const.add (contDiff_const.mul contDiff_id)))

theorem terminalMorseCapRadius_deriv (s origin direction t : ℝ) {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) :
    deriv (terminalMorseCapRadius s origin direction r) t =
      s * deriv r (origin + direction * t) * direction := by
  have hpoint : HasDerivAt (fun x : ℝ => origin + direction * x) direction t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul direction).const_add origin
  have h := ((hr.differentiable (by simp) (origin + direction * t)).hasDerivAt.comp
    t hpoint).const_mul s
  change deriv (fun x => s * r (origin + direction * x)) t = _
  simpa only [Function.comp_apply, mul_assoc] using h.deriv

theorem terminalMorseCapRadius_second (s origin direction t : ℝ) {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (hdir : direction ^ 2 = 1) :
    deriv (deriv (terminalMorseCapRadius s origin direction r)) t =
      s * deriv (deriv r) (origin + direction * t) := by
  have hr' : ContDiff ℝ ∞ (deriv r) := (contDiff_infty_iff_deriv.mp hr).2
  have hd : deriv (terminalMorseCapRadius s origin direction r) =
      fun x => s * deriv r (origin + direction * x) * direction :=
    funext (fun x => terminalMorseCapRadius_deriv s origin direction x hr)
  rw [hd, deriv_mul_const_field]
  change deriv (terminalMorseCapRadius s origin direction (deriv r)) t * direction = _
  rw [terminalMorseCapRadius_deriv s origin direction t hr']
  calc
    _ = s * deriv (deriv r) (origin + direction * t) * direction ^ 2 := by ring
    _ = _ := by rw [hdir, mul_one]

/-- The actual logarithmic short-cap length is bounded below absolutely. -/
theorem terminalMorse_short_length_lower : (1 / 6 : ℝ) ≤ morseShortLeftCapLength := by
  have hlog := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6 / 5)
  have hratio : (3 / 2 : ℝ) / (5 / 4) = 6 / 5 := by norm_num
  have hd := log_div (by norm_num : (3 / 2 : ℝ) ≠ 0) (by norm_num : (5 / 4 : ℝ) ≠ 0)
  rw [hratio] at hd
  unfold morseShortLeftCapLength morseShortLeftCapCut morseCellLeftCut
  norm_num at hlog
  linarith only [hlog, hd]

/-- Frequency action places a complete mass-scale window in the cap
and supplies an absolute lower bound for the cutoff action. -/
theorem terminalMorse_short_layer_window {A j t : ℝ}
    (hA : 0 < A) (hj : 0 < j) (haction : 1000 ≤ j * sqrt A)
    (ht : t ∈ Icc (morseShortLeftCapLength / 4) (morseShortLeftCapLength / 2)) :
    0 < j * sqrt A / 2 ∧ 0 ≤ t ∧
      t + 1 / (j * sqrt A / 2) ≤ morseShortLeftCapLength ∧
      j * sqrt A / 48 ≤ (j * sqrt A / 2) * t := by
  have htau : 0 < j * sqrt A := mul_pos hj (sqrt_pos.mpr hA)
  have hm : 0 < j * sqrt A / 2 := div_pos htau (by norm_num)
  have hL := morseShortLeftCapLength_pos
  have hlong := mul_le_mul_of_nonneg_left terminalMorse_short_length_lower htau.le
  have hwindow : 1 / (j * sqrt A / 2) ≤ morseShortLeftCapLength / 4 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith only [hlong, haction]
  have hlayer := mul_le_mul_of_nonneg_left ht.1 hm.le
  exact ⟨hm, by linarith only [ht.1, hL],
    by linarith only [ht.2, hwindow, hL],
    by nlinarith only [hlayer, hlong]⟩

/-- All geometric and potential bounds refer to the actual normalized
Morse radius, with the physical dilation retained. -/
theorem terminalMorse_short_cap_geometry {A B j s t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r) (ht : t ∈ Icc 0 morseShortLeftCapLength) :
    let R := terminalMorseCapRadius s morseCellLeftCut 1 r
    0 < R t ∧ 0 < deriv R t ∧
      deriv (deriv R) t = -morseRho A B (morseCellLeftCut + t) * R t ∧
      (j * sqrt A / 2) ^ 2 ≤ j ^ 2 * (-morseRho A B (morseCellLeftCut + t)) ∧
      |j ^ 2 * (-morseRho A B (morseCellLeftCut + t))| ≤ 4 * (j * sqrt A / 2) ^ 2 := by
  dsimp only
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hx : morseCellLeftCut + t ∈ Icc morseCellLeftCut morseShortLeftCapCut := by
    constructor
    · linarith only [ht.1]
    · dsimp only [morseShortLeftCapLength] at ht
      linarith only [ht.2]
  have hturn : morseShortLeftCapCut < morseRightTurn A B :=
    (morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)
  have hxleft : morseCellLeftCut + t ∈ Icc morseCellLeftCut (morseRightTurn A B) :=
    ⟨hx.1, hx.2.trans hturn.le⟩
  have hcollar : (0 : ℝ) ≤ morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
  have hend : morseRightTurn A B ≤ morseRightCapEnd A B (1 / 100) :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hxwide : morseCellLeftCut + t ∈ Icc (morseCellLeftCut - morseJoinCollarWidth)
      (morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth) :=
    ⟨by linarith only [hx.1, hcollar],
      by linarith only [hxleft.2, hend, hcollar]⟩
  have hp := (hr.left_half _ hxleft).2.1
  have hv := hr.speed_pos _ hxwide
  have hlo := morseShortLeftCap_negRho_lower hB hAB hx.2
  have hhi := morseLeftCap_negRho_upper hB hAB hx.1
  have hmass : (j * sqrt A / 2) ^ 2 = j ^ 2 * A / 4 := by
    rw [div_pow, mul_pow, sq_sqrt hA.le]
    norm_num
  have hq0 : 0 ≤ j ^ 2 * (-morseRho A B (morseCellLeftCut + t)) :=
    mul_nonneg (sq_nonneg _) ((div_pos hA (by norm_num)).le.trans hlo)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [terminalMorseCapRadius, one_mul] using mul_pos hs hp
  · rw [terminalMorseCapRadius_deriv s morseCellLeftCut 1 t hr.smooth]
    simpa only [one_mul, mul_one] using mul_pos hs hv
  · rw [terminalMorseCapRadius_second s morseCellLeftCut 1 t hr.smooth (by norm_num)]
    simp only [one_mul, terminalMorseCapRadius]
    rw [hr.equation _ hxwide]
    ring
  · rw [hmass]
    have h := mul_le_mul_of_nonneg_left hlo (sq_nonneg j)
    nlinarith only [h]
  · rw [abs_of_nonneg hq0, hmass]
    have h := mul_le_mul_of_nonneg_left hhi (sq_nonneg j)
    nlinarith only [h]

/-- The normalized stand-in from the actual incoming construction
satisfies uniform attenuation on the fixed middle-quarter layer.
The inputs are its physical homogeneous equation and the exact profile
identity; the pulled-back equation and both potential bounds are proved. -/
theorem terminalMorse_short_cap_layer_bounds {A B j s scale t : ℝ} {r w u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hs : 0 < s) (hscale : scale ≠ 0)
    (hr : IsNormalizedMorseCell A B r) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut morseShortLeftCapCut,
      w (s * r x) = scale * (s * deriv r x))
    (hode : ∀ x ∈ Icc morseCellLeftCut morseShortLeftCapCut,
      radialJacobi (j ^ 2) w u (s * r x) = 0)
    (hjoin : u (s * r morseCellLeftCut) = 1)
    (hwall : u (s * r morseShortLeftCapCut) = 0)
    (haction : 1000 ≤ j * sqrt A)
    (ht : t ∈ Icc (morseShortLeftCapLength / 4) (morseShortLeftCapLength / 2)) :
    |u (s * r (morseCellLeftCut + t))| ≤ exp (-(j * sqrt A / 48)) ∧
      |deriv u (s * r (morseCellLeftCut + t))| ≤
        (3 * j * sqrt A / (s * deriv r (morseCellLeftCut + t))) *
          exp (-(j * sqrt A / 48)) := by
  let R := terminalMorseCapRadius s morseCellLeftCut 1 r
  let p : ℝ → ℝ := fun x => u (R x)
  let m : ℝ := j * sqrt A / 2
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  obtain ⟨hm, ht0, hwindow, hactiont⟩ := terminalMorse_short_layer_window hA hj haction ht
  have hR : ContDiff ℝ ∞ R := terminalMorseCapRadius_smooth _ _ _ hr.smooth
  have hp : ContDiff ℝ ∞ p := hu.comp hR
  have hmap (x : ℝ) (hx : x ∈ Icc 0 morseShortLeftCapLength) :
      morseCellLeftCut + x ∈ Icc morseCellLeftCut morseShortLeftCapCut := by
    constructor
    · linarith only [hx.1]
    · dsimp only [morseShortLeftCapLength] at hx
      linarith only [hx.2]
  have hweightR (x : ℝ) (hx : x ∈ Icc 0 morseShortLeftCapLength) :
      w (R x) = scale * deriv R x := by
    change w (s * r (morseCellLeftCut + 1 * x)) =
      scale * deriv (terminalMorseCapRadius s morseCellLeftCut 1 r) x
    rw [terminalMorseCapRadius_deriv s morseCellLeftCut 1 x hr.smooth]
    simpa only [one_mul, mul_one] using hweight _ (hmap x hx)
  have hodeR (x : ℝ) (hx : x ∈ Icc 0 morseShortLeftCapLength) :
      radialJacobi (j ^ 2) w u (R x) = 0 := by
    simpa only [R, terminalMorseCapRadius, one_mul] using hode _ (hmap x hx)
  obtain ⟨hfirst, hsecond⟩ := r07_cap_pullback_system morseShortLeftCapLength_pos
    hscale hR hw hu hweightR hodeR
  have hpd : deriv p = fun x => deriv u (R x) * deriv R x :=
    funext (fun x => ((hu.differentiable (by simp) (R x)).hasDerivAt.comp x
      (hR.differentiable (by simp) x).hasDerivAt).deriv)
  have heq (x : ℝ) (hx : x ∈ Icc 0 morseShortLeftCapLength) :
      deriv (deriv p) x = (j ^ 2 * (-morseRho A B (morseCellLeftCut + x))) * p x := by
    have hg := terminalMorse_short_cap_geometry (j := j) hB hAB hs hr hx
    calc
      _ = (j ^ 2 * deriv (deriv R) x / R x) * u (R x) := by
        rw [hpd]
        exact (hsecond x hx).deriv
      _ = _ := by
        rw [hg.2.2.1]
        dsimp only [p]
        field_simp [hg.1.ne']
        ring
  have hlo (x : ℝ) (hx : x ∈ Icc 0 morseShortLeftCapLength) :
      m ^ 2 ≤ j ^ 2 * (-morseRho A B (morseCellLeftCut + x)) :=
    (terminalMorse_short_cap_geometry (j := j) hB hAB hs hr hx).2.2.2.1
  have hhi (x : ℝ) (hx : x ∈ Icc t (t + 1 / m)) :
      |j ^ 2 * (-morseRho A B (morseCellLeftCut + x))| ≤ 4 * m ^ 2 :=
    (terminalMorse_short_cap_geometry (j := j) hB hAB hs hr
      (Icc_subset_Icc ht0 hwindow hx)).2.2.2.2
  have hp0 : p 0 = 1 := by simpa only [p, R, terminalMorseCapRadius, mul_zero, add_zero] using hjoin
  have hpL : p morseShortLeftCapLength = 0 := by
    have hend : morseCellLeftCut + morseShortLeftCapLength = morseShortLeftCapCut := by
      dsimp only [morseShortLeftCapLength]
      ring
    simpa only [p, R, terminalMorseCapRadius, one_mul, hend] using hwall
  have hjet := terminalCap_model_layer_bounds (m := m) (A := 1) (C := 4) hm
    (by norm_num) (by norm_num) ht0 hwindow (fun _ _ => hp.contDiffAt) heq hlo hhi hp0 hpL
  have htin : t ∈ Icc 0 morseShortLeftCapLength :=
    ⟨ht0, (le_add_of_nonneg_right (one_div_nonneg.mpr hm.le)).trans hwindow⟩
  have hspeed : 0 < deriv R t := (terminalMorse_short_cap_geometry (j := j) hB hAB hs hr htin).2.1
  have hexp : exp (-(m * t)) ≤ exp (-(j * sqrt A / 48)) :=
    exp_le_exp.mpr (neg_le_neg hactiont)
  have hvalue : |p t| ≤ exp (-(j * sqrt A / 48)) := by
    have hv : |p t| ≤ exp (-(m * t)) := by
      simpa only [one_mul, sub_zero] using hjet.1
    exact hv.trans hexp
  have hderiv : |deriv u (R t)| ≤ (6 * m / deriv R t) * exp (-(m * t)) := by
    have he : deriv p t = deriv u (R t) * deriv R t := congrFun hpd t
    have hb : |deriv u (R t)| * deriv R t ≤ 6 * m * exp (-(m * t)) := by
      rw [← abs_of_pos hspeed, ← abs_mul, ← he]
      simpa only [one_mul, sub_zero, show (2 + 4 : ℝ) = 6 by norm_num] using hjet.2
    have := (le_div_iff₀ hspeed).mpr hb
    convert this using 1 <;> ring
  have hcoef : 6 * m / deriv R t = 3 * j * sqrt A / (s * deriv r (morseCellLeftCut + t)) := by
    change 6 * (j * sqrt A / 2) / deriv (terminalMorseCapRadius s morseCellLeftCut 1 r) t = _
    rw [terminalMorseCapRadius_deriv s morseCellLeftCut 1 t hr.smooth]
    simp only [one_mul, mul_one]
    ring
  have hderiv' := hderiv.trans (mul_le_mul_of_nonneg_left hexp
    (div_nonneg (mul_nonneg (by norm_num) hm.le) hspeed.le))
  rw [hcoef] at hderiv'
  exact ⟨by simpa only [p, R, terminalMorseCapRadius, one_mul] using hvalue,
    by simpa only [R, terminalMorseCapRadius, one_mul] using hderiv'⟩

end ContinuousFlexibility.Radial
