import ContinuousFlexibility.Radial.TerminalMorseLongGeometry
import ContinuousFlexibility.Radial.TerminalCapCoshComparison

/-!
# Attenuation of the actual normalized long-cap stand-in

The physical solution is zero at the turning point, has positive initial
slope there, and is one at the far cap endpoint. The true radial profile
identity yields its Morse equation. Positivity is first proved on the
whole cap using the nonnegative potential; a positive lower bound is used
only on the later subinterval beyond log 4.

This proves both attenuated jets on a fixed cutoff layer without imposing
a false mass lower bound at the turning point.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

theorem terminalMorse_long_cap_layer_bounds {A B j s scale t : ℝ} {r w u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hs : 0 < s) (hscale : scale ≠ 0)
    (hA₀ : A ≤ 1 / 1000) (hBA : A ^ 9 / (9 : ℝ) ^ 9 ≤ B)
    (hr : IsNormalizedMorseCell A B r) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = scale * (s * deriv r x))
    (hode : ∀ x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)),
      radialJacobi (j ^ 2) w u (s * r x) = 0)
    (hzero : u (s * r (morseRightTurn A B)) = 0)
    (hinit : 0 < deriv u (s * r (morseRightTurn A B)))
    (hjoin : u (s * r (morseRightCapEnd A B (1 / 100))) = 1)
    (haction : 1000000000 ≤ j * sqrt A)
    (ht : t ∈ Icc (morseRightCapLength A (1 / 100) / 4)
      (morseRightCapLength A (1 / 100) / 2)) :
    |u (s * r (morseRightTurn A B + t))| ≤ 2 * exp (-(j * sqrt A / 50000000)) ∧
      |deriv u (s * r (morseRightTurn A B + t))| ≤
        (6 * j * sqrt B / (s * deriv r (morseRightTurn A B + t))) *
          exp (-(j * sqrt A / 50000000)) := by
  let R := terminalMorseCapRadius s (morseRightTurn A B) 1 r
  let p : ℝ → ℝ := fun x => u (R x)
  let q : ℝ → ℝ := fun x => j ^ 2 * (-morseRho A B (morseRightTurn A B + x))
  let L : ℝ := morseRightCapLength A (1 / 100)
  let m : ℝ := j * sqrt B / 2
  let sigma : ℝ := j * sqrt A / 50000000
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 < L := morseRightCapLength_pos hA (by norm_num)
  obtain ⟨hm, htfar, hwindow, hbudget⟩ :=
    terminalMorse_long_layer_window hA hB hj hA₀ hBA haction ht
  change 0 < m at hm
  change t + 1 / m ≤ 3 * L / 4 at hwindow
  change sigma ≤ m * (L / 4) at hbudget
  have ht0 : 0 ≤ t := (log_pos (by norm_num : (1 : ℝ) < 4)).le.trans htfar
  have hwindowL : t + 1 / m ≤ L := by linarith only [hwindow, hL]
  have hsubwindow : Icc t (t + 1 / m) ⊆ Icc 0 L := Icc_subset_Icc ht0 hwindowL
  have hR : ContDiff ℝ ∞ R := terminalMorseCapRadius_smooth _ _ _ hr.smooth
  have hp : ContDiff ℝ ∞ p := hu.comp hR
  have hpd : deriv p = fun x => deriv u (R x) * deriv R x :=
    funext (fun x => ((hu.differentiable (by simp) (R x)).hasDerivAt.comp x
      (hR.differentiable (by simp) x).hasDerivAt).deriv)
  have hmap (x : ℝ) (hx : x ∈ Icc 0 L) :
      morseRightTurn A B + x ∈
        Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)) := by
    constructor
    · linarith only [hx.1]
    · change morseRightTurn A B + x ≤ morseRightTurn A B + L
      linarith only [hx.2]
  have hweightR (x : ℝ) (hx : x ∈ Icc 0 L) :
      w (R x) = scale * deriv R x := by
    change w (s * r (morseRightTurn A B + 1 * x)) =
      scale * deriv (terminalMorseCapRadius s (morseRightTurn A B) 1 r) x
    rw [terminalMorseCapRadius_deriv s (morseRightTurn A B) 1 x hr.smooth]
    simpa only [one_mul, mul_one] using hweight _ (hmap x hx)
  have hodeR (x : ℝ) (hx : x ∈ Icc 0 L) : radialJacobi (j ^ 2) w u (R x) = 0 := by
    simpa only [R, terminalMorseCapRadius, one_mul] using hode _ (hmap x hx)
  obtain ⟨_, hsecond⟩ := r07_cap_pullback_system hL hscale hR hw hu hweightR hodeR
  have heq (x : ℝ) (hx : x ∈ Icc 0 L) : deriv (deriv p) x = q x * p x := by
    have hg := terminalMorse_long_cap_geometry (j := j) hB hAB hs hr hx
    have hRx : R x ≠ 0 := hg.1.ne'
    have hReq : deriv (deriv R) x = -morseRho A B (morseRightTurn A B + x) * R x :=
      hg.2.2.1
    calc
      _ = (j ^ 2 * deriv (deriv R) x / R x) * u (R x) := by
        rw [hpd]
        exact (hsecond x hx).deriv
      _ = _ := by
        rw [hReq]
        dsimp only [p, q]
        field_simp [hRx] <;> ring
  have hq (x : ℝ) (hx : x ∈ Icc 0 L) : 0 ≤ q x ∧ q x ≤ (j * sqrt B) ^ 2 :=
    ⟨(terminalMorse_long_cap_geometry (j := j) hB hAB hs hr hx).2.2.2.1,
      (terminalMorse_long_cap_geometry (j := j) hB hAB hs hr hx).2.2.2.2.1⟩
  have hp0 : p 0 = 0 := by
    simpa only [p, R, terminalMorseCapRadius, mul_zero, add_zero] using hzero
  have hpL : p L = 1 := by
    simpa only [p, R, terminalMorseCapRadius, one_mul, L, morseRightCapEnd] using hjoin
  have hinitp : 0 < deriv p 0 := by
    rw [hpd]
    exact mul_pos (by simpa only [R, terminalMorseCapRadius, mul_zero, add_zero] using hinit)
      (terminalMorse_long_cap_geometry (j := j) hB hAB hs hr ⟨le_rfl, hL.le⟩).2.1
  have hd (x : ℝ) (_ : x ∈ Icc 0 L) : HasDerivAt p (deriv p x) x :=
    (hp.differentiable (by simp) x).hasDerivAt
  have hdd (x : ℝ) (hx : x ∈ Icc 0 L) : HasDerivAt (deriv p) (q x * p x) x := by
    rw [← heq x hx]
    exact ((contDiff_infty_iff_deriv.mp hp).2.differentiable (by simp) x).hasDerivAt
  have hpos := dirichlet_nonneg hd hdd hq hp0 hinitp
  have hslope := dirichlet_deriv_pos_Icc hd hdd hq hp0 hinitp
  have hheight (x : ℝ) (hx : x ∈ Icc t (t + 1 / m)) :
      |p x| ≤ 2 * exp (-sigma) := by
    have hxfull := hsubwindow hx
    have hfar : log 4 ≤ x := htfar.trans hx.1
    have hsub : Icc x L ⊆ Icc 0 L := Icc_subset_Icc hxfull.1 le_rfl
    have hqlower (y : ℝ) (hy : y ∈ Icc x L) : m ^ 2 ≤ q y :=
      (terminalMorse_long_cap_geometry (j := j) hB hAB hs hr (hsub hy)).2.2.2.2.2
        (hfar.trans hy.1)
    have hg := terminalCap_exponential_of_cosh hxfull.2 hp
      (fun y hy => heq y (hsub hy)) hqlower
      (fun y hy => hpos y (hsub hy)) (hslope x hxfull).le
    have hv : p x ≤ 2 * exp (-(m * (L - x))) := by
      simpa only [hpL, mul_one] using hg
    have hdist : L / 4 ≤ L - x := by linarith only [hx.2, hwindow]
    have hsigma : sigma ≤ m * (L - x) :=
      hbudget.trans (mul_le_mul_of_nonneg_left hdist hm.le)
    rw [abs_of_nonneg (hpos x hxfull)]
    exact hv.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hsigma)) (by norm_num))
  have hqupper (x : ℝ) (hx : x ∈ Icc t (t + 1 / m)) : |q x| ≤ 4 * m ^ 2 := by
    rw [abs_of_nonneg (hq x (hsubwindow hx)).1]
    calc
      _ ≤ (j * sqrt B) ^ 2 := (hq x (hsubwindow hx)).2
      _ = _ := by dsimp only [m]; ring
  have hderivp := innerBuffer_mass_scale_derivative (x := t) (u := p) (V := q)
    hm (by positivity : 0 ≤ 2 * exp (-sigma)) (by norm_num : (0 : ℝ) ≤ 4)
    (fun x _ => hp.differentiable (by simp) x)
    (fun x _ => (contDiff_infty_iff_deriv.mp hp).2.differentiable (by simp) x)
    hheight hqupper (fun x hx => heq x (hsubwindow hx))
  have htin : t ∈ Icc t (t + 1 / m) :=
    ⟨le_rfl, le_add_of_nonneg_right (one_div_nonneg.mpr hm.le)⟩
  have hspeed : 0 < deriv R t :=
    (terminalMorse_long_cap_geometry (j := j) hB hAB hs hr (hsubwindow htin)).2.1
  have hphysical : |deriv u (R t)| ≤ (12 * m / deriv R t) * exp (-sigma) := by
    have he : deriv p t = deriv u (R t) * deriv R t := congrFun hpd t
    have hb : |deriv u (R t)| * deriv R t ≤ 12 * m * exp (-sigma) := by
      rw [← abs_of_pos hspeed, ← abs_mul, ← he]
      convert hderivp using 1 <;> ring
    have := (le_div_iff₀ hspeed).mpr hb
    convert this using 1 <;> ring
  have hcoef : 12 * m / deriv R t = 6 * j * sqrt B / (s * deriv r (morseRightTurn A B + t)) := by
    change 12 * (j * sqrt B / 2) /
      deriv (terminalMorseCapRadius s (morseRightTurn A B) 1 r) t = _
    rw [terminalMorseCapRadius_deriv s (morseRightTurn A B) 1 t hr.smooth]
    simp only [one_mul, mul_one]
    ring
  rw [hcoef] at hphysical
  exact ⟨by simpa only [p, R, terminalMorseCapRadius, one_mul, sigma] using hheight t htin,
    by simpa only [R, terminalMorseCapRadius, one_mul, sigma] using hphysical⟩

end ContinuousFlexibility.Radial
