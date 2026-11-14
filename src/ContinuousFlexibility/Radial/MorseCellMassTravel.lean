module

public import ContinuousFlexibility.Radial.MorseLeftCapBounds
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Travel and velocity mass on an actual Morse cell

The short cap contains a fixed interval on which the Morse coefficient is
negative with size at least a fixed multiple of `A`. The same interval gives
the lower velocity mass bound by the radius equation. The upper mass bound
uses the total radius increment and does not use the growing model length.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def morseShortLeftCapCut : ℝ := -log (5 / 4)

def morseShortLeftCapLength : ℝ := morseShortLeftCapCut - morseCellLeftCut

def morseLeftCapTravel (A B : ℝ) : ℝ :=
  ∫ x in morseCellLeftCut..morseLeftTurn A B, sqrt (-morseRho A B x)

def morseLeftCellVelocityMass (A B : ℝ) (r : ℝ → ℝ) : ℝ :=
  ∫ x in morseCellLeftCut..morseRightTurn A B, (deriv r x) ^ 2

theorem morseCellLeftCut_lt_shortLeftCapCut : morseCellLeftCut < morseShortLeftCapCut := by
  unfold morseCellLeftCut morseShortLeftCapCut
  exact neg_lt_neg (log_lt_log (by norm_num) (by norm_num))

theorem morseShortLeftCapLength_pos : 0 < morseShortLeftCapLength :=
  sub_pos.mpr morseCellLeftCut_lt_shortLeftCapCut

theorem morseShortLeftCapCut_lt_leftTurn {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    morseShortLeftCapCut < morseLeftTurn A B := by
  have hcut : morseShortLeftCapCut < 0 := neg_lt_zero.mpr (log_pos (by norm_num))
  obtain ⟨_, _, hlo, hhi⟩ := morseRootT_bounds hB hAB
  have hturn : 0 < morseLeftTurn A B :=
    neg_pos.mpr (log_neg ((by norm_num : (0 : ℝ) < 1 / 2).trans hlo) hhi)
  exact hcut.trans hturn

private theorem exp_neg_morseShortLeftCapCut : exp (-morseShortLeftCapCut) = 5 / 4 := by
  rw [morseShortLeftCapCut, neg_neg, exp_log (by norm_num : (0 : ℝ) < 5 / 4)]

private theorem cell_exp_neg_two (x : ℝ) : exp (-2 * x) = exp (-x) ^ 2 := by
  rw [pow_two, ← exp_add]
  congr 1
  ring

theorem morseShortLeftCap_negRho_lower {A B x : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hx : x ≤ morseShortLeftCapCut) : A / 4 ≤ -morseRho A B x := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have ht : (5 / 4 : ℝ) ≤ exp (-x) := by
    rw [← exp_neg_morseShortLeftCapCut]
    exact exp_le_exp.mpr (neg_le_neg hx)
  have hp : (1 / 4 : ℝ) ≤ exp (-x) ^ 2 - exp (-x) := calc
    _ = 1 * (1 / 4 : ℝ) := by norm_num
    _ ≤ exp (-x) * (exp (-x) - 1) :=
      mul_le_mul (by linarith only [ht]) (by linarith only [ht]) (by norm_num) (exp_pos _).le
    _ = _ := by ring
  calc
    A / 4 = A * (1 / 4) := by ring
    _ ≤ A * (exp (-x) ^ 2 - exp (-x)) := mul_le_mul_of_nonneg_left hp hA.le
    _ ≤ A * (exp (-x) ^ 2 - exp (-x)) + B := le_add_of_nonneg_right hB.le
    _ = _ := by rw [morseRho, cell_exp_neg_two]; ring

theorem morseLeftCap_negRho_upper {A B x : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hx : morseCellLeftCut ≤ x) : -morseRho A B x ≤ A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have ht : exp (-x) ≤ 3 / 2 := by
    rw [← exp_neg_morseCellLeftCut]
    exact exp_le_exp.mpr (neg_le_neg hx)
  have hp : exp (-x) ^ 2 - exp (-x) ≤ 3 / 4 := calc
    _ = exp (-x) * (exp (-x) - 1) := by ring
    _ ≤ exp (-x) * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith only [ht]) (exp_pos _).le
    _ ≤ (3 / 2 : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_right ht (by norm_num)
    _ = _ := by norm_num
  calc
    -morseRho A B x = A * (exp (-x) ^ 2 - exp (-x)) + B := by
      rw [morseRho, cell_exp_neg_two]
      ring
    _ ≤ A * (3 / 4) + B := add_le_add_left (mul_le_mul_of_nonneg_left hp hA.le) B
    _ ≤ _ := by linarith only [hAB]

private theorem morseLeftCap_length_le {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    morseLeftTurn A B - morseCellLeftCut ≤ 3 / 2 := by
  have hlo := (morseRootT_bounds hB hAB).2.2.1
  have hl := log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlo.le
  rw [one_div, log_inv] at hl
  have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h32 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  unfold morseLeftTurn morseCellLeftCut
  linarith only [hl, h2, h32]

/-- The actual short cap contributes a fixed multiple of `sqrt A` to the travel. -/
theorem morseLeftCap_travel_bounds {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    morseShortLeftCapLength / 2 * sqrt A ≤ morseLeftCapTravel A B ∧
      morseLeftCapTravel A B ≤ (3 / 2 : ℝ) * sqrt A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hau := morseCellLeftCut_lt_shortLeftCapCut.le
  have hul := (morseShortLeftCapCut_lt_leftTurn hB hAB).le
  have hal := hau.trans hul
  let f : ℝ → ℝ := fun x => sqrt (-morseRho A B x)
  have hf : Continuous f := (contDiff_morseRho A B).continuous.neg.sqrt
  have hcl : Continuous (fun _ : ℝ => sqrt (A / 4)) := continuous_const
  have hcu : Continuous (fun _ : ℝ => sqrt A) := continuous_const
  have hlo : (∫ _ in morseCellLeftCut..morseShortLeftCapCut, sqrt (A / 4)) ≤
      ∫ x in morseCellLeftCut..morseShortLeftCapCut, f x :=
    intervalIntegral.integral_mono_on hau (hcl.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _) (fun x hx => sqrt_le_sqrt (morseShortLeftCap_negRho_lower hB hAB hx.2))
  have hext : (∫ x in morseCellLeftCut..morseShortLeftCapCut, f x) ≤ morseLeftCapTravel A B :=
    intervalIntegral.integral_mono_interval le_rfl hau hul
      (Filter.Eventually.of_forall (fun x => sqrt_nonneg (-morseRho A B x))) (hf.intervalIntegrable _ _)
  have hhi : morseLeftCapTravel A B ≤ ∫ _ in morseCellLeftCut..morseLeftTurn A B, sqrt A :=
    intervalIntegral.integral_mono_on hal (hf.intervalIntegrable _ _)
      (hcu.intervalIntegrable _ _) (fun x hx => sqrt_le_sqrt (morseLeftCap_negRho_upper hB hAB hx.1))
  have hs : sqrt (A / 4) = sqrt A / 2 := by
    rw [sqrt_div hA.le, show sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
  rw [intervalIntegral.integral_const, smul_eq_mul, hs] at hlo
  rw [intervalIntegral.integral_const, smul_eq_mul] at hhi
  refine ⟨?_, hhi.trans (mul_le_mul_of_nonneg_right (morseLeftCap_length_le hB hAB) (sqrt_nonneg _))⟩
  calc
    _ = (morseShortLeftCapCut - morseCellLeftCut) * (sqrt A / 2) := by
      unfold morseShortLeftCapLength
      ring
    _ ≤ _ := hlo.trans hext

/-- The mass is estimated on the same radius as the backwards Volterra bounds. -/
theorem morseLeftCell_velocity_mass_bounds {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hr₀ : r (morseRightTurn A B) = 1)
    (hclose : |r morseCellLeftCut - 1| ≤ 6 * A)
    (hEq : ∀ x ∈ Icc morseCellLeftCut (morseRightTurn A B),
      deriv (deriv r) x = -morseRho A B x * r x)
    (hrpos : ∀ x ∈ Icc morseCellLeftCut (morseRightTurn A B), 0 ≤ r x)
    (hv₀ : A / 4 ≤ deriv r morseCellLeftCut)
    (hv : ∀ x ∈ Icc morseCellLeftCut (morseRightTurn A B),
      0 ≤ deriv r x ∧ deriv r x ≤ 7 * A) :
    morseShortLeftCapLength / 16 * A ^ 2 ≤ morseLeftCellVelocityMass A B r ∧
      morseLeftCellVelocityMass A B r ≤ 42 * A ^ 2 := by
  let a := morseCellLeftCut
  let u := morseShortLeftCapCut
  let b := morseRightTurn A B
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hau : a ≤ u := morseCellLeftCut_lt_shortLeftCapCut.le
  have hub : u ≤ b := ((morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)).le
  have hab : a ≤ b := hau.trans hub
  have hvD := (contDiff_infty_iff_deriv.mp hr).2
  have hmono : MonotoneOn (deriv r) (Icc a u) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a u) hvD.continuous.continuousOn
      (hvD.differentiable (by simp)).differentiableOn ?_
    intro x hx
    have hxu : x ∈ Icc a u := interior_subset hx
    have hxb : x ∈ Icc a b := ⟨hxu.1, hxu.2.trans hub⟩
    rw [hEq x hxb]
    exact mul_nonneg ((div_nonneg hA.le (by norm_num : (0 : ℝ) ≤ 4)).trans
      (morseShortLeftCap_negRho_lower hB hAB hxu.2)) (hrpos x hxb)
  have hlow (x : ℝ) (hx : x ∈ Icc a u) : A / 4 ≤ deriv r x :=
    hv₀.trans (hmono (left_mem_Icc.mpr hau) hx hx.1)
  have hsq : Continuous (fun x => (deriv r x) ^ 2) := hvD.continuous.pow 2
  have hci : Continuous (fun _ : ℝ => (A / 4) ^ 2) := continuous_const
  have hlo : (∫ _ in a..u, (A / 4) ^ 2) ≤ ∫ x in a..u, (deriv r x) ^ 2 :=
    intervalIntegral.integral_mono_on hau (hci.intervalIntegrable _ _) (hsq.intervalIntegrable _ _)
      (fun x hx => pow_le_pow_left₀ (div_nonneg hA.le (by norm_num)) (hlow x hx) 2)
  have hext : (∫ x in a..u, (deriv r x) ^ 2) ≤ morseLeftCellVelocityMass A B r :=
    intervalIntegral.integral_mono_interval le_rfl hau hub
      (Filter.Eventually.of_forall (fun x => sq_nonneg (deriv r x))) (hsq.intervalIntegrable _ _)
  have hi : IntervalIntegrable (deriv r) volume a b := hvD.continuous.intervalIntegrable _ _
  have hFTC : (∫ x in a..b, deriv r x) = r b - r a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hr.differentiable (by simp) x).hasDerivAt) hi
  have hcv : Continuous (fun x => 7 * A * deriv r x) := continuous_const.mul hvD.continuous
  have hhi : morseLeftCellVelocityMass A B r ≤ ∫ x in a..b, 7 * A * deriv r x :=
    intervalIntegral.integral_mono_on hab (hsq.intervalIntegrable _ _) (hcv.intervalIntegrable _ _)
      (fun x hx => by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hv x hx).2 (hv x hx).1)
  have hspan : r b - r a ≤ 6 * A := by
    have hrb : r b = 1 := hr₀
    have hra : |r a - 1| ≤ 6 * A := hclose
    rw [hrb]
    linarith only [(abs_le.mp hra).1]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlo
  rw [intervalIntegral.integral_const_mul, hFTC] at hhi
  constructor
  · calc
      _ = (u - a) * (A / 4) ^ 2 := by unfold morseShortLeftCapLength; dsimp only [u, a]; ring
      _ ≤ _ := hlo.trans hext
  · calc
      _ ≤ (7 * A) * (r b - r a) := hhi
      _ ≤ (7 * A) * (6 * A) := mul_le_mul_of_nonneg_left hspan (by positivity)
      _ = _ := by ring

/-- One retained-cell solution carries the left mass estimate and the two cap travel bounds. -/
theorem exists_morseRadius_retainedCell_mass_travel {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hA₀ : A ≤ 1 / 1000) (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9) :
    let b := morseRightTurn A B
    let e := morseRightCapEnd A B (1 / 100)
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r b = 1 ∧ deriv r b = (1 / 100 : ℝ) * A ^ 5 ∧
      (∀ x ∈ Icc morseCellLeftCut e,
        deriv (deriv r) x = -morseRho A B x * r x ∧ 0 < r x ∧ 0 < deriv r x) ∧
      (morseShortLeftCapLength / 16 * A ^ 2 ≤ morseLeftCellVelocityMass A B r ∧
        morseLeftCellVelocityMass A B r ≤ 42 * A ^ 2) ∧
      (morseShortLeftCapLength / 2 * sqrt A ≤ morseLeftCapTravel A B ∧
        morseLeftCapTravel A B ≤ (3 / 2 : ℝ) * sqrt A) ∧
      (((1 / 100 : ℝ) / 2 / sqrt (2 * (9 : ℝ) ^ 9)) * sqrt A ≤ morseRightCapTravel A B (1 / 100) ∧
        morseRightCapTravel A B (1 / 100) ≤ (1 / 100 : ℝ) * sqrt A) := by
  let b := morseRightTurn A B
  let e := morseRightCapEnd A B (1 / 100)
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hbe : b ≤ e :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hsub : Icc morseCellLeftCut b ⊆ Icc morseCellLeftCut e :=
    fun _ hx => ⟨hx.1, hx.2.trans hbe⟩
  have ha : morseCellLeftCut ∈ Icc morseCellLeftCut b :=
    left_mem_Icc.mpr (morseCellLeftCut_lt_rightTurn hB hAB).le
  have hV : 0 < (1 / 100 : ℝ) * A ^ 5 := by positivity
  obtain ⟨r, hr, hr₀, hv₀, hEq, hBounds, _, _, hvC, _, _, _⟩ :=
    exists_morseRadius_retainedCell hB hAB hA₀ hBAlo hBAhi
  have hMass := morseLeftCell_velocity_mass_bounds hB hAB hr hr₀ (hBounds _ (hsub ha)).1
    (fun x hx => hEq x (hsub hx)) (fun x hx => (hBounds x (hsub hx)).2.1.le) hvC
    (fun x hx => ⟨(hV.trans_le (hBounds x (hsub hx)).2.2.2.1).le, (hBounds x (hsub hx)).2.2.2.2⟩)
  refine ⟨r, hr, hr₀, hv₀, ?_, hMass, morseLeftCap_travel_bounds hB hAB,
    morseRightCap_travel_bounds_fixed hB hAB (hA₀.trans (by norm_num)) hBAlo hBAhi⟩
  intro x hx
  exact ⟨hEq x hx, (hBounds x hx).2.1, hV.trans_le (hBounds x hx).2.2.2.1⟩

/-- The inverse of the actual radius on the interval used for the change of variables. -/
def morseCellModelCoordinate (r : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  Function.invFunOn r (Icc a b)

def morseCellRadialProfile (r : ℝ → ℝ) (a b scale z : ℝ) : ℝ :=
  scale * deriv r (morseCellModelCoordinate r a b z)

theorem morseCell_strictMonoOn {r : ℝ → ℝ} {a b : ℝ} (hr : ContDiff ℝ ∞ r)
    (hv : ∀ x ∈ Icc a b, 0 < deriv r x) : StrictMonoOn r (Icc a b) :=
  strictMonoOn_of_deriv_pos (convex_Icc a b) hr.continuous.continuousOn
    (fun x hx => hv x (interior_subset hx))

theorem morseCellModelCoordinate_apply {r : ℝ → ℝ} {a b x : ℝ}
    (hmono : StrictMonoOn r (Icc a b)) (hx : x ∈ Icc a b) :
    morseCellModelCoordinate r a b (r x) = x :=
  hmono.injOn.leftInvOn_invFunOn hx

theorem morseCellModelCoordinate_right {r : ℝ → ℝ} {a b z : ℝ}
    (hab : a ≤ b) (hr : ContDiff ℝ ∞ r) (hmono : StrictMonoOn r (Icc a b))
    (hz : z ∈ Icc (r a) (r b)) :
    morseCellModelCoordinate r a b z ∈ Icc a b ∧ r (morseCellModelCoordinate r a b z) = z := by
  have him := hr.continuous.continuousOn.image_Icc_of_monotoneOn hab hmono.monotoneOn
  have hmem : z ∈ r '' Icc a b := by rwa [him]
  exact Function.invFunOn_pos hmem

theorem morseCellRadialProfile_apply {r : ℝ → ℝ} {a b x : ℝ} (scale : ℝ)
    (hmono : StrictMonoOn r (Icc a b)) (hx : x ∈ Icc a b) :
    morseCellRadialProfile r a b scale (r x) = scale * deriv r x := by
  rw [morseCellRadialProfile, morseCellModelCoordinate_apply hmono hx]

private theorem morseCell_interval_change {r g F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hr : ContDiff ℝ ∞ r) (hmono : StrictMonoOn r (Icc a b))
    (hv : ∀ x ∈ Icc a b, 0 < deriv r x) (hF : ContinuousOn F (Icc a b))
    (heq : ∀ x ∈ Icc a b, deriv r x * g (r x) = F x) :
    IntervalIntegrable g volume (r a) (r b) ∧
      (∫ z in r a..r b, g z) = ∫ x in a..b, F x := by
  have hrange : r a ≤ r b := hmono.monotoneOn (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have him := hr.continuous.continuousOn.image_Ioc_of_strictMonoOn hab hmono
  have hD (x : ℝ) (_hx : x ∈ Ioc a b) : HasDerivWithinAt r (deriv r x) (Ioc a b) x :=
    (hr.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hi : InjOn r (Ioc a b) := hmono.injOn.mono Ioc_subset_Icc_self
  have hprod : EqOn (fun x => |deriv r x| • g (r x)) F (Ioc a b) := by
    intro x hx
    have hx' := Ioc_subset_Icc_self hx
    simpa only [abs_of_pos (hv x hx'), smul_eq_mul] using heq x hx'
  have hFI : IntegrableOn F (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hF.intervalIntegrable_of_Icc hab)
  have hGI := hFI.congr_fun hprod.symm measurableSet_Ioc
  have hint := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc hD hi g).mpr hGI
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hD hi g
  rw [him] at hint hchange
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hrange).mpr hint, ?_⟩
  rw [intervalIntegral.integral_of_le hrange, intervalIntegral.integral_of_le hab, hchange]
  exact setIntegral_congr_fun measurableSet_Ioc hprod

/-- The core spectral mass and the transfer resistance used in Section 6.
Both formulas use the inverse of this radius on the stated interval. -/
theorem morseCell_coreTransfer_mass_resistance_change {r : ℝ → ℝ} {a b scale : ℝ}
    (hab : a ≤ b) (hscale : 0 < scale) (hr : ContDiff ℝ ∞ r)
    (hrpos : ∀ x ∈ Icc a b, 0 < r x) (hv : ∀ x ∈ Icc a b, 0 < deriv r x) :
    let w := morseCellRadialProfile r a b scale
    IntervalIntegrable (fun z => 12 * w z / z ^ 2) volume (r a) (r b) ∧
      IntervalIntegrable (fun z => 1 / w z) volume (r a) (r b) ∧
      (∫ z in r a..r b, 12 * w z / z ^ 2) =
        12 * scale * (∫ x in a..b, (deriv r x / r x) ^ 2) ∧
      (∫ z in r a..r b, 1 / w z) = (b - a) / scale := by
  let w := morseCellRadialProfile r a b scale
  have hm := morseCell_strictMonoOn hr hv
  have hq : ContinuousOn (fun x => deriv r x / r x) (Icc a b) :=
    (contDiff_infty_iff_deriv.mp hr).2.continuous.continuousOn.div hr.continuous.continuousOn
      (fun x hx => (hrpos x hx).ne')
  have hc : ContinuousOn (fun x => 12 * scale * (deriv r x / r x) ^ 2) (Icc a b) :=
    continuousOn_const.mul (hq.pow 2)
  have hF (x : ℝ) (hx : x ∈ Icc a b) :
      deriv r x * (12 * w (r x) / r x ^ 2) = 12 * scale * (deriv r x / r x) ^ 2 := by
    rw [show w (r x) = scale * deriv r x from morseCellRadialProfile_apply scale hm hx, div_pow]
    ring
  have hG (x : ℝ) (hx : x ∈ Icc a b) : deriv r x * (1 / w (r x)) = 1 / scale := by
    rw [show w (r x) = scale * deriv r x from morseCellRadialProfile_apply scale hm hx]
    field_simp [hscale.ne', (hv x hx).ne']
  obtain ⟨hmI, hmE⟩ := morseCell_interval_change (g := fun z => 12 * w z / z ^ 2)
    hab hr hm hv hc hF
  obtain ⟨hrI, hrE⟩ := morseCell_interval_change (g := fun z => 1 / w z) hab hr hm hv
    (continuousOn_const : ContinuousOn (fun _ : ℝ => 1 / scale) (Icc a b)) hG
  refine ⟨hmI, hrI, ?_, ?_⟩
  · rw [hmE, intervalIntegral.integral_const_mul]
  · rw [hrE, intervalIntegral.integral_const, smul_eq_mul, mul_one_div]

/-- The Section 5 chain densities on any subinterval of the same model cell.
The physical profile uses the inverse on the entire retained interval. -/
theorem morseCell_chain_mass_resistance_change {r : ℝ → ℝ} {a b c d scale : ℝ}
    (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b) (hscale : 0 < scale)
    (hr : ContDiff ℝ ∞ r) (hrpos : ∀ x ∈ Icc a b, 0 < r x)
    (hv : ∀ x ∈ Icc a b, 0 < deriv r x) :
    let w := morseCellRadialProfile r a b scale
    IntervalIntegrable (fun z => w z * z ^ 6) volume (r c) (r d) ∧
      IntervalIntegrable (fun z => (w z * z ^ 8)⁻¹) volume (r c) (r d) ∧
      (∫ z in r c..r d, w z * z ^ 6) =
        scale * (∫ x in c..d, (deriv r x) ^ 2 * r x ^ 6) ∧
      (∫ z in r c..r d, (w z * z ^ 8)⁻¹) =
        scale⁻¹ * (∫ x in c..d, (r x ^ 8)⁻¹) := by
  let w := morseCellRadialProfile r a b scale
  have hm := morseCell_strictMonoOn hr hv
  have hv' : ∀ x ∈ Icc c d, 0 < deriv r x := fun x hx => hv x (hsub hx)
  have hV : ContinuousOn (deriv r) (Icc c d) :=
    (contDiff_infty_iff_deriv.mp hr).2.continuous.continuousOn
  have hR : ContinuousOn r (Icc c d) := hr.continuous.continuousOn
  have hpow_ne (x : ℝ) (hx : x ∈ Icc c d) : r x ^ 8 ≠ 0 :=
    pow_ne_zero 8 (hrpos x (hsub hx)).ne'
  have hMc : ContinuousOn (fun x => scale * ((deriv r x) ^ 2 * r x ^ 6)) (Icc c d) :=
    continuousOn_const.mul ((hV.pow 2).mul (hR.pow 6))
  have hRc : ContinuousOn (fun x => scale⁻¹ * (r x ^ 8)⁻¹) (Icc c d) :=
    continuousOn_const.mul ((hR.pow 8).inv₀ hpow_ne)
  have hw (x : ℝ) (hx : x ∈ Icc c d) : w (r x) = scale * deriv r x :=
    morseCellRadialProfile_apply scale hm (hsub hx)
  have hM (x : ℝ) (hx : x ∈ Icc c d) :
      deriv r x * (w (r x) * r x ^ 6) = scale * ((deriv r x) ^ 2 * r x ^ 6) := by
    rw [hw x hx]
    ring
  have hS (x : ℝ) (hx : x ∈ Icc c d) :
      deriv r x * (w (r x) * r x ^ 8)⁻¹ = scale⁻¹ * (r x ^ 8)⁻¹ := by
    rw [hw x hx, ← div_eq_mul_inv]
    apply (div_eq_iff (mul_ne_zero (mul_ne_zero hscale.ne' (hv' x hx).ne') (hpow_ne x hx))).mpr
    calc
      deriv r x = deriv r x * ((scale⁻¹ * scale) * ((r x ^ 8)⁻¹ * r x ^ 8)) := by
        rw [inv_mul_cancel₀ hscale.ne', inv_mul_cancel₀ (hpow_ne x hx), one_mul, mul_one]
      _ = _ := by ring
  obtain ⟨hMi, hMe⟩ := morseCell_interval_change (g := fun z => w z * z ^ 6)
    hcd hr (hm.mono hsub) hv' hMc hM
  obtain ⟨hRi, hRe⟩ := morseCell_interval_change (g := fun z => (w z * z ^ 8)⁻¹)
    hcd hr (hm.mono hsub) hv' hRc hS
  refine ⟨hMi, hRi, ?_, ?_⟩
  · rw [hMe, intervalIntegral.integral_const_mul]
  · rw [hRe, intervalIntegral.integral_const_mul]

/-- The literal chain integrals on the mass interval and on the retained
right cap, using one profile for both parts of the same cell. -/
theorem morseRetainedCell_chain_mass_resistance_change {A B scale : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hscale : 0 < scale)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hrpos : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)), 0 < r x)
    (hv : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)), 0 < deriv r x) :
    let a := morseCellLeftCut
    let b := morseRightTurn A B
    let e := morseRightCapEnd A B (1 / 100)
    let w := morseCellRadialProfile r a e scale
    (∫ z in r a..r b, w z * z ^ 6) = scale * (∫ x in a..b, (deriv r x) ^ 2 * r x ^ 6) ∧
      (∫ z in r a..r b, (w z * z ^ 8)⁻¹) = scale⁻¹ * (∫ x in a..b, (r x ^ 8)⁻¹) ∧
      (∫ z in r b..r e, w z * z ^ 6) = scale * (∫ x in b..e, (deriv r x) ^ 2 * r x ^ 6) ∧
      (∫ z in r b..r e, (w z * z ^ 8)⁻¹) = scale⁻¹ * (∫ x in b..e, (r x ^ 8)⁻¹) := by
  let a := morseCellLeftCut
  let b := morseRightTurn A B
  let e := morseRightCapEnd A B (1 / 100)
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hab : a ≤ b := (morseCellLeftCut_lt_rightTurn hB hAB).le
  have hbe : b ≤ e :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hI : Icc a b ⊆ Icc a e := fun _ hx => ⟨hx.1, hx.2.trans hbe⟩
  have hJ : Icc b e ⊆ Icc a e := fun _ hx => ⟨hab.trans hx.1, hx.2⟩
  obtain ⟨_, _, hmI, hrI⟩ := morseCell_chain_mass_resistance_change hab hI hscale hr hrpos hv
  obtain ⟨_, _, hmJ, hrJ⟩ := morseCell_chain_mass_resistance_change hbe hJ hscale hr hrpos hv
  exact ⟨hmI, hrI, hmJ, hrJ⟩

end ContinuousFlexibility.Radial
