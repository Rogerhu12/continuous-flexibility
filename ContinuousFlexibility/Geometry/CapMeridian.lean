import ContinuousFlexibility.Scalar.Coordinates
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# An actual smooth meridian for the fixed cap

Section 2, `lem:fixed-cap`, uses a symmetric turning function and its
integrated unit tangent. Here the turning function is explicitly chosen,
and all endpoint collars come from exact constant values. The coordinate
speed identity is Euclidean; the norm on `ℝ × ℝ` is not used as Euclidean.
This file constructs a meridian, not a closed surface.
-/

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def capTurn (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

def capRadialVelocity (t : ℝ) : ℝ := Real.cos (Real.pi * capTurn t)

def capDownwardVelocity (t : ℝ) : ℝ := Real.sin (Real.pi * capTurn t)

def capRadialOffset (t : ℝ) : ℝ := ∫ u in 0..t, capRadialVelocity u

def capHeightDrop (t : ℝ) : ℝ := ∫ u in 0..t, capDownwardVelocity u

def capDrop : ℝ := capHeightDrop 1

def capMeridianRadius (R L s : ℝ) : ℝ := R + L * capRadialOffset (s / L)

def capMeridianHeight (h L s : ℝ) : ℝ := h - L * capHeightDrop (s / L)

def capMeridian (R h L s : ℝ) : ℝ × ℝ :=
  (capMeridianRadius R L s, capMeridianHeight h L s)

def capLength (h lo ε : ℝ) : ℝ := (|h - lo| + ε) / capDrop

theorem contDiff_capTurn : ContDiff ℝ ∞ capTurn :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem capTurn_nonneg (t : ℝ) : 0 ≤ capTurn t := Real.smoothTransition.nonneg _

theorem capTurn_le_one (t : ℝ) : capTurn t ≤ 1 := Real.smoothTransition.le_one _

theorem monotone_capTurn : Monotone capTurn := by
  intro s t hst
  exact Real.smoothTransition.monotone (by linarith)

theorem capTurn_eq_zero {t : ℝ} (ht : t ≤ 1 / 4) : capTurn t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem capTurn_eq_one {t : ℝ} (ht : 3 / 4 ≤ t) : capTurn t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem smoothTransition_reflection (t : ℝ) :
    Real.smoothTransition (1 - t) = 1 - Real.smoothTransition t := by
  have hd := (Real.smoothTransition.pos_denom t).ne'
  unfold Real.smoothTransition
  rw [show 1 - (1 - t) = t by ring, add_comm (expNegInvGlue (1 - t))]
  field_simp
  ring

theorem capTurn_reflection (t : ℝ) : capTurn (1 - t) = 1 - capTurn t := by
  unfold capTurn
  rw [show 2 * (1 - t) - 1 / 2 = 1 - (2 * t - 1 / 2) by ring]
  exact smoothTransition_reflection _

@[simp] theorem capTurn_half : capTurn (1 / 2) = 1 / 2 := by
  have h := capTurn_reflection (1 / 2)
  norm_num at h ⊢
  linarith

theorem capTurn_pos {t : ℝ} (ht : 1 / 4 < t) : 0 < capTurn t :=
  Real.smoothTransition.pos_of_pos (by linarith)

theorem capTurn_lt_one {t : ℝ} (ht : t < 3 / 4) : capTurn t < 1 :=
  Real.smoothTransition.lt_one_of_lt_one (by linarith)

theorem contDiff_capRadialVelocity : ContDiff ℝ ∞ capRadialVelocity :=
  (contDiff_const.mul contDiff_capTurn).cos

theorem contDiff_capDownwardVelocity : ContDiff ℝ ∞ capDownwardVelocity :=
  (contDiff_const.mul contDiff_capTurn).sin

theorem capRadialVelocity_reflection (t : ℝ) :
    capRadialVelocity (1 - t) = -capRadialVelocity t := by
  unfold capRadialVelocity
  rw [capTurn_reflection, mul_sub, mul_one, Real.cos_pi_sub]

theorem capDownwardVelocity_reflection (t : ℝ) :
    capDownwardVelocity (1 - t) = capDownwardVelocity t := by
  unfold capDownwardVelocity
  rw [capTurn_reflection, mul_sub, mul_one, Real.sin_pi_sub]

theorem capRadialVelocity_eq_one {t : ℝ} (ht : t ≤ 1 / 4) :
    capRadialVelocity t = 1 := by simp [capRadialVelocity, capTurn_eq_zero ht]

theorem capDownwardVelocity_eq_zero_left {t : ℝ} (ht : t ≤ 1 / 4) :
    capDownwardVelocity t = 0 := by simp [capDownwardVelocity, capTurn_eq_zero ht]

theorem capRadialVelocity_eq_neg_one {t : ℝ} (ht : 3 / 4 ≤ t) :
    capRadialVelocity t = -1 := by simp [capRadialVelocity, capTurn_eq_one ht]

theorem capDownwardVelocity_eq_zero_right {t : ℝ} (ht : 3 / 4 ≤ t) :
    capDownwardVelocity t = 0 := by simp [capDownwardVelocity, capTurn_eq_one ht]

theorem capRadialVelocity_nonneg {t : ℝ} (ht : t ≤ 1 / 2) :
    0 ≤ capRadialVelocity t := by
  have hturn := monotone_capTurn ht
  rw [capTurn_half] at hturn
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (capTurn_nonneg t)]
  · nlinarith [mul_le_mul_of_nonneg_left hturn Real.pi_pos.le]

theorem capDownwardVelocity_nonneg (t : ℝ) : 0 ≤ capDownwardVelocity t := by
  apply Real.sin_nonneg_of_mem_Icc
  constructor
  · exact mul_nonneg Real.pi_pos.le (capTurn_nonneg t)
  · nlinarith [mul_le_mul_of_nonneg_left (capTurn_le_one t) Real.pi_pos.le]

theorem capDownwardVelocity_pos {t : ℝ} (ht : t ∈ Ioo (1 / 4) (3 / 4)) :
    0 < capDownwardVelocity t := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos Real.pi_pos (capTurn_pos ht.1)
  · nlinarith [mul_lt_mul_of_pos_left (capTurn_lt_one ht.2) Real.pi_pos]

@[simp] theorem capDownwardVelocity_half : capDownwardVelocity (1 / 2) = 1 := by
  rw [capDownwardVelocity, capTurn_half,
    show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]

theorem hasDerivAt_capRadialOffset (t : ℝ) :
    HasDerivAt capRadialOffset (capRadialVelocity t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (contDiff_capRadialVelocity.continuous.intervalIntegrable _ _)
    contDiff_capRadialVelocity.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    contDiff_capRadialVelocity.continuous.continuousAt

theorem hasDerivAt_capHeightDrop (t : ℝ) :
    HasDerivAt capHeightDrop (capDownwardVelocity t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (contDiff_capDownwardVelocity.continuous.intervalIntegrable _ _)
    contDiff_capDownwardVelocity.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    contDiff_capDownwardVelocity.continuous.continuousAt

theorem contDiff_capRadialOffset : ContDiff ℝ ∞ capRadialOffset := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (hasDerivAt_capRadialOffset t).differentiableAt, ?_⟩
  have h : deriv capRadialOffset = capRadialVelocity :=
    funext fun t => (hasDerivAt_capRadialOffset t).deriv
  rw [h]
  exact contDiff_capRadialVelocity

theorem contDiff_capHeightDrop : ContDiff ℝ ∞ capHeightDrop := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (hasDerivAt_capHeightDrop t).differentiableAt, ?_⟩
  have h : deriv capHeightDrop = capDownwardVelocity :=
    funext fun t => (hasDerivAt_capHeightDrop t).deriv
  rw [h]
  exact contDiff_capDownwardVelocity

theorem capRadialOffset_eq_left {t : ℝ} (ht : t ≤ 1 / 4) : capRadialOffset t = t := by
  have h := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := t)
    (f := capRadialVelocity) (g := fun _ => (1 : ℝ)) (fun u hu =>
      capRadialVelocity_eq_one (hu.2.trans (max_le (by norm_num) ht)))
  simpa [capRadialOffset] using h

theorem capHeightDrop_eq_left {t : ℝ} (ht : t ≤ 1 / 4) : capHeightDrop t = 0 := by
  have h := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := t)
    (f := capDownwardVelocity) (g := fun _ => (0 : ℝ)) (fun u hu =>
      capDownwardVelocity_eq_zero_left (hu.2.trans (max_le (by norm_num) ht)))
  simpa [capHeightDrop] using h

@[simp] theorem capRadialOffset_zero : capRadialOffset 0 = 0 := by simp [capRadialOffset]

@[simp] theorem capHeightDrop_zero : capHeightDrop 0 = 0 := by simp [capHeightDrop]

@[simp] theorem capRadialOffset_one : capRadialOffset 1 = 0 := by
  have h := intervalIntegral.integral_comp_sub_left capRadialVelocity (a := 0) (b := 1) 1
  simp only [capRadialVelocity_reflection, intervalIntegral.integral_neg, sub_self,
    sub_zero] at h
  change -capRadialOffset 1 = capRadialOffset 1 at h
  linarith

theorem capRadialOffset_reflection (t : ℝ) :
    capRadialOffset (1 - t) = capRadialOffset t := by
  have hc := contDiff_capRadialVelocity.continuous
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t 1)
  have hr := intervalIntegral.integral_comp_sub_left capRadialVelocity (a := t) (b := 1) 1
  simp only [capRadialVelocity_reflection, intervalIntegral.integral_neg, sub_self] at hr
  change -(∫ u in t..1, capRadialVelocity u) = capRadialOffset (1 - t) at hr
  change capRadialOffset t + (∫ u in t..1, capRadialVelocity u) = capRadialOffset 1 at hs
  rw [capRadialOffset_one] at hs
  linarith

theorem capHeightDrop_reflection (t : ℝ) :
    capHeightDrop (1 - t) = capDrop - capHeightDrop t := by
  have hc := contDiff_capDownwardVelocity.continuous
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t 1)
  have hr := intervalIntegral.integral_comp_sub_left capDownwardVelocity (a := t) (b := 1) 1
  simp only [capDownwardVelocity_reflection, sub_self] at hr
  change (∫ u in t..1, capDownwardVelocity u) = capHeightDrop (1 - t) at hr
  change capHeightDrop t + (∫ u in t..1, capDownwardVelocity u) = capDrop at hs
  linarith

theorem capRadialOffset_eq_right {t : ℝ} (ht : 3 / 4 ≤ t) :
    capRadialOffset t = 1 - t := by
  rw [← capRadialOffset_reflection t, capRadialOffset_eq_left (by linarith)]

theorem capHeightDrop_eq_right {t : ℝ} (ht : 3 / 4 ≤ t) :
    capHeightDrop t = capDrop := by
  have h := capHeightDrop_reflection t
  rw [capHeightDrop_eq_left (by linarith)] at h
  linarith

theorem capDrop_pos : 0 < capDrop := by
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
    contDiff_capDownwardVelocity.continuous.continuousOn
  · intro t _
    exact capDownwardVelocity_nonneg t
  · exact ⟨1 / 2, by norm_num, by rw [capDownwardVelocity_half]; norm_num⟩

theorem capRadialOffset_pos_left {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    0 < capRadialOffset t := by
  apply intervalIntegral.integral_pos ht contDiff_capRadialVelocity.continuous.continuousOn
  · intro u hu
    exact capRadialVelocity_nonneg (hu.2.trans ht')
  · exact ⟨0, ⟨le_rfl, ht.le⟩, by rw [capRadialVelocity_eq_one (by norm_num)]; norm_num⟩

theorem capRadialOffset_pos {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < capRadialOffset t := by
  by_cases h : t ≤ 1 / 2
  · exact capRadialOffset_pos_left ht.1 h
  · rw [← capRadialOffset_reflection t]
    exact capRadialOffset_pos_left (by linarith [ht.2]) (by linarith)

theorem capRadialOffset_nonneg {t : ℝ} (ht : t ∈ Icc 0 1) : 0 ≤ capRadialOffset t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst t
    simp
  rcases lt_or_eq_of_le ht.2 with h' | h'
  · exact (capRadialOffset_pos ⟨h, h'⟩).le
  · subst t
    simp

theorem monotone_capHeightDrop : Monotone capHeightDrop :=
  monotone_of_hasDerivAt_nonneg hasDerivAt_capHeightDrop capDownwardVelocity_nonneg

theorem strictMonoOn_capHeightDrop : StrictMonoOn capHeightDrop (Icc (1 / 4) (3 / 4)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) contDiff_capHeightDrop.continuous.continuousOn
  intro t ht
  rw [(hasDerivAt_capHeightDrop t).deriv]
  exact capDownwardVelocity_pos (by simpa only [interior_Icc] using ht)

/-- Any interval meeting the interior turning region has a strict height drop. -/
theorem capHeightDrop_lt {s t : ℝ} (hst : s < t) (hs : s < 3 / 4) (ht : 1 / 4 < t) :
    capHeightDrop s < capHeightDrop t := by
  have ha : max s (1 / 4) ∈ Icc (1 / 4 : ℝ) (3 / 4) :=
    ⟨le_max_right _ _, max_le hs.le (by norm_num)⟩
  have hb : min t (3 / 4) ∈ Icc (1 / 4 : ℝ) (3 / 4) :=
    ⟨le_min ht.le (by norm_num), min_le_right _ _⟩
  have hab : max s (1 / 4 : ℝ) < min t (3 / 4) :=
    max_lt (lt_min hst hs) (lt_min ht (by norm_num))
  have hleft : capHeightDrop (max s (1 / 4)) = capHeightDrop s := by
    by_cases h : s ≤ 1 / 4
    · rw [max_eq_right h, capHeightDrop_eq_left le_rfl, capHeightDrop_eq_left h]
    · rw [max_eq_left (le_of_not_ge h)]
  have hright : capHeightDrop (min t (3 / 4)) = capHeightDrop t := by
    by_cases h : 3 / 4 ≤ t
    · rw [min_eq_right h, capHeightDrop_eq_right le_rfl, capHeightDrop_eq_right h]
    · rw [min_eq_left (le_of_not_ge h)]
  simpa only [hleft, hright] using strictMonoOn_capHeightDrop ha hb hab

theorem capNormalizedMeridian_ne_of_lt {s t : ℝ} (hst : s < t) :
    (capRadialOffset s, capHeightDrop s) ≠ (capRadialOffset t, capHeightDrop t) := by
  intro heq
  have hr := congrArg Prod.fst heq
  have hz := congrArg Prod.snd heq
  dsimp at hr hz
  by_cases ht : t ≤ 1 / 4
  · rw [capRadialOffset_eq_left (hst.le.trans ht), capRadialOffset_eq_left ht] at hr
    exact hst.ne hr
  by_cases hs : 3 / 4 ≤ s
  · rw [capRadialOffset_eq_right hs, capRadialOffset_eq_right (hs.trans hst.le)] at hr
    linarith
  exact (capHeightDrop_lt hst (lt_of_not_ge hs) (lt_of_not_ge ht)).ne hz

theorem capNormalizedMeridian_injective :
    Function.Injective (fun t => (capRadialOffset t, capHeightDrop t)) := by
  intro s t h
  rcases lt_trichotomy s t with hst | hst | hst
  · exact False.elim (capNormalizedMeridian_ne_of_lt hst h)
  · exact hst
  · exact False.elim (capNormalizedMeridian_ne_of_lt hst h.symm)

theorem contDiff_capMeridianRadius (R L : ℝ) : ContDiff ℝ ∞ (capMeridianRadius R L) :=
  contDiff_const.add (contDiff_const.mul (contDiff_capRadialOffset.comp (contDiff_id.div_const L)))

theorem contDiff_capMeridianHeight (h L : ℝ) : ContDiff ℝ ∞ (capMeridianHeight h L) :=
  contDiff_const.sub (contDiff_const.mul (contDiff_capHeightDrop.comp (contDiff_id.div_const L)))

theorem contDiff_capMeridian (R h L : ℝ) : ContDiff ℝ ∞ (capMeridian R h L) :=
  (contDiff_capMeridianRadius R L).prodMk (contDiff_capMeridianHeight h L)

theorem hasDerivAt_capMeridianRadius (R : ℝ) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    HasDerivAt (capMeridianRadius R L) (capRadialVelocity (s / L)) s := by
  have hd := ((hasDerivAt_capRadialOffset (s / L)).comp s
    ((hasDerivAt_id s).div_const L)).const_mul L
  convert! hd.const_add R using 1
  field_simp [hL.ne']

theorem hasDerivAt_capMeridianHeight (h : ℝ) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    HasDerivAt (capMeridianHeight h L) (-capDownwardVelocity (s / L)) s := by
  have hd := ((hasDerivAt_capHeightDrop (s / L)).comp s
    ((hasDerivAt_id s).div_const L)).const_mul L
  convert! (hasDerivAt_const s h).sub hd using 1
  field_simp [hL.ne']
  ring

theorem capMeridian_unit_speed (R h : ℝ) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    deriv (capMeridianRadius R L) s ^ 2 + deriv (capMeridianHeight h L) s ^ 2 = 1 := by
  rw [(hasDerivAt_capMeridianRadius R hL s).deriv,
    (hasDerivAt_capMeridianHeight h hL s).deriv]
  dsimp [capRadialVelocity, capDownwardVelocity]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * capTurn (s / L))]

theorem capMeridian_injective (R h : ℝ) {L : ℝ} (hL : 0 < L) :
    Function.Injective (capMeridian R h L) := by
  intro s t heq
  have hr := congrArg Prod.fst heq
  have hz := congrArg Prod.snd heq
  dsimp [capMeridian, capMeridianRadius, capMeridianHeight] at hr hz
  have hr' : capRadialOffset (s / L) = capRadialOffset (t / L) := by nlinarith
  have hz' : capHeightDrop (s / L) = capHeightDrop (t / L) := by nlinarith
  have hst := capNormalizedMeridian_injective (Prod.ext hr' hz')
  exact (div_left_inj' hL.ne').mp hst

theorem capMeridianRadius_eq_left (R : ℝ) {L s : ℝ} (hL : 0 < L) (hs : s ≤ L / 4) :
    capMeridianRadius R L s = R + s := by
  have ht : s / L ≤ 1 / 4 := (div_le_iff₀ hL).2 (by linarith)
  rw [capMeridianRadius, capRadialOffset_eq_left ht]
  field_simp [hL.ne']

theorem capMeridianHeight_eq_left (h : ℝ) {L s : ℝ} (hL : 0 < L) (hs : s ≤ L / 4) :
    capMeridianHeight h L s = h := by
  have ht : s / L ≤ 1 / 4 := (div_le_iff₀ hL).2 (by linarith)
  simp [capMeridianHeight, capHeightDrop_eq_left ht]

theorem capMeridianRadius_eq_right (R : ℝ) {L s : ℝ} (hL : 0 < L) (hs : 3 * L / 4 ≤ s) :
    capMeridianRadius R L s = R + L - s := by
  have ht : 3 / 4 ≤ s / L := (le_div_iff₀ hL).2 (by linarith)
  rw [capMeridianRadius, capRadialOffset_eq_right ht]
  field_simp [hL.ne']
  ring

theorem capMeridianHeight_eq_right (h : ℝ) {L s : ℝ} (hL : 0 < L) (hs : 3 * L / 4 ≤ s) :
    capMeridianHeight h L s = h - L * capDrop := by
  have ht : 3 / 4 ≤ s / L := (le_div_iff₀ hL).2 (by linarith)
  rw [capMeridianHeight, capHeightDrop_eq_right ht]

theorem capMeridianRadius_core_le (R : ℝ) {L s : ℝ} (hL : 0 < L) (hs : s ∈ Icc 0 L) :
    R ≤ capMeridianRadius R L s := by
  have ht : s / L ∈ Icc 0 1 := ⟨div_nonneg hs.1 hL.le, (div_le_one hL).2 hs.2⟩
  have hh := mul_nonneg hL.le (capRadialOffset_nonneg ht)
  dsimp [capMeridianRadius]
  linarith

theorem capMeridianRadius_core_lt (R : ℝ) {L s : ℝ} (hL : 0 < L) (hs : s ∈ Ioo 0 L) :
    R < capMeridianRadius R L s := by
  have ht : s / L ∈ Ioo 0 1 := ⟨div_pos hs.1 hL, (div_lt_one hL).2 hs.2⟩
  have hh := mul_pos hL (capRadialOffset_pos ht)
  dsimp [capMeridianRadius]
  linarith

theorem capMeridian_top_axis {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L) (h : ℝ) :
    capMeridian R h L (-R) = (0, h) := by
  have hs : -R ≤ L / 4 := by linarith
  simp [capMeridian, capMeridianRadius_eq_left R hL hs, capMeridianHeight_eq_left h hL hs]

theorem capMeridian_bottom_axis {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L) (h : ℝ) :
    capMeridian R h L (L + R) = (0, h - L * capDrop) := by
  have hs : 3 * L / 4 ≤ L + R := by linarith
  rw [capMeridian, capMeridianRadius_eq_right R hL hs, capMeridianHeight_eq_right h hL hs]
  congr 1
  ring

theorem capMeridianRadius_pos {R L s : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hs : s ∈ Ioo (-R) (L + R)) : 0 < capMeridianRadius R L s := by
  by_cases h0 : s < 0
  · rw [capMeridianRadius_eq_left R hL (by linarith)]
    linarith [hs.1]
  by_cases h1 : L < s
  · rw [capMeridianRadius_eq_right R hL (by linarith)]
    linarith [hs.2]
  exact hR.trans_le (capMeridianRadius_core_le R hL ⟨le_of_not_gt h0, le_of_not_gt h1⟩)

theorem capMeridianRadius_zero_iff {R L s : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hs : s ∈ Icc (-R) (L + R)) :
    capMeridianRadius R L s = 0 ↔ s = -R ∨ s = L + R := by
  constructor
  · intro hz
    by_cases hleft : s = -R
    · exact Or.inl hleft
    by_cases hright : s = L + R
    · exact Or.inr hright
    have hp := capMeridianRadius_pos hR hL
      (show s ∈ Ioo (-R) (L + R) from
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hleft), lt_of_le_of_ne hs.2 hright⟩)
    linarith
  · rintro (rfl | rfl)
    · rw [capMeridianRadius_eq_left R hL (by linarith)]
      ring
    · rw [capMeridianRadius_eq_right R hL (by linarith)]
      ring

theorem capMeridianRadius_nonneg {R L s : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hs : s ∈ Icc (-R) (L + R)) : 0 ≤ capMeridianRadius R L s := by
  rcases eq_or_lt_of_le hs.1 with hleft | hleft
  · subst s
    rw [capMeridianRadius_eq_left R hL (by linarith)]
    simp
  rcases lt_or_eq_of_le hs.2 with hright | hright
  · exact (capMeridianRadius_pos hR hL ⟨hleft, hright⟩).le
  · subst s
    rw [capMeridianRadius_eq_right R hL (by linarith)]
    simp [add_comm]

theorem capLength_pos (h lo : ℝ) {ε : ℝ} (hε : 0 < ε) : 0 < capLength h lo ε :=
  div_pos (add_pos_of_nonneg_of_pos (abs_nonneg _) hε) capDrop_pos

theorem capLength_bottom_le (h lo ε : ℝ) :
    h - capLength h lo ε * capDrop ≤ lo - ε := by
  rw [capLength, div_mul_cancel₀ _ capDrop_pos.ne']
  linarith [le_abs_self (h - lo)]

theorem capLength_bottom_lt (h lo : ℝ) {ε : ℝ} (hε : 0 < ε) :
    h - capLength h lo ε * capDrop < lo :=
  (capLength_bottom_le h lo ε).trans_lt (by linarith)

theorem capMeridianHeight_capLength_below (h lo : ℝ) {ε : ℝ} (hε : 0 < ε) :
    capMeridianHeight h (capLength h lo ε) (capLength h lo ε) < lo := by
  have hL := capLength_pos h lo hε
  rw [capMeridianHeight_eq_right h hL (by linarith)]
  exact capLength_bottom_lt h lo hε

@[simp] theorem capMeridian_zero (R h L : ℝ) : capMeridian R h L 0 = (R, h) := by
  simp [capMeridian, capMeridianRadius, capMeridianHeight]

theorem capMeridian_length (R h : ℝ) {L : ℝ} (hL : 0 < L) :
    capMeridian R h L L = (R, h - L * capDrop) := by
  simp [capMeridian, capMeridianRadius, capMeridianHeight, div_self hL.ne', capDrop]

theorem capMeridian_left_collar (R h : ℝ) {L s : ℝ} (hL : 0 < L) (hs : s ≤ L / 4) :
    capMeridian R h L s = (R + s, h) := by
  simp only [capMeridian, capMeridianRadius_eq_left R hL hs, capMeridianHeight_eq_left h hL hs]

theorem capMeridian_right_collar (R h : ℝ) {L s : ℝ} (hL : 0 < L) (hs : 3 * L / 4 ≤ s) :
    capMeridian R h L s = (R + L - s, h - L * capDrop) := by
  simp only [capMeridian, capMeridianRadius_eq_right R hL hs, capMeridianHeight_eq_right h hL hs]

theorem hasDerivAt_capMeridian (R h : ℝ) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    HasDerivAt (capMeridian R h L)
      (capRadialVelocity (s / L), -capDownwardVelocity (s / L)) s :=
  (hasDerivAt_capMeridianRadius R hL s).prodMk (hasDerivAt_capMeridianHeight h hL s)

theorem capMeridian_deriv_ne_zero (R h : ℝ) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    deriv (capMeridian R h L) s ≠ 0 := by
  intro hz
  rw [(hasDerivAt_capMeridian R h hL s).deriv] at hz
  have hr := congrArg Prod.fst hz
  have hh := congrArg Prod.snd hz
  dsimp [capRadialVelocity, capDownwardVelocity] at hr hh
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * capTurn (s / L))]

theorem antitone_capMeridianHeight (h : ℝ) {L : ℝ} (hL : 0 < L) :
    Antitone (capMeridianHeight h L) := by
  intro s t hst
  have hd := monotone_capHeightDrop ((div_le_div_iff_of_pos_right hL).2 hst)
  have hm := mul_le_mul_of_nonneg_left hd hL.le
  dsimp [capMeridianHeight]
  linarith

theorem capMeridianHeight_strict {h L s t : ℝ} (hL : 0 < L)
    (hst : s < t) (hs : s < 3 * L / 4) (ht : L / 4 < t) :
    capMeridianHeight h L t < capMeridianHeight h L s := by
  have hd := capHeightDrop_lt ((div_lt_div_iff_of_pos_right hL).2 hst)
    ((div_lt_iff₀ hL).2 (show s < (3 / 4) * L by linarith))
    ((lt_div_iff₀ hL).2 (show (1 / 4) * L < t by linarith))
  have hm := mul_lt_mul_of_pos_left hd hL
  dsimp [capMeridianHeight]
  linarith

theorem capHeightDrop_bounds (t : ℝ) : 0 ≤ capHeightDrop t ∧ capHeightDrop t ≤ capDrop := by
  constructor
  · by_cases ht : t ≤ 1 / 4
    · rw [capHeightDrop_eq_left ht]
    · have h := monotone_capHeightDrop (show 0 ≤ t by linarith)
      simpa only [capHeightDrop_zero] using h
  · by_cases ht : 3 / 4 ≤ t
    · rw [capHeightDrop_eq_right ht]
    · exact monotone_capHeightDrop (show t ≤ 1 by linarith)

theorem capMeridianHeight_bounds (h : ℝ) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    h - L * capDrop ≤ capMeridianHeight h L s ∧ capMeridianHeight h L s ≤ h := by
  have hb := capHeightDrop_bounds (s / L)
  have h0 := mul_nonneg hL.le hb.1
  have h1 := mul_le_mul_of_nonneg_left hb.2 hL.le
  dsimp [capMeridianHeight]
  constructor <;> linarith

end ContinuousFlexibility
