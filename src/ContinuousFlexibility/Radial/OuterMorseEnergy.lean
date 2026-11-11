import ContinuousFlexibility.Radial.TransitionTransfer
import ContinuousFlexibility.Radial.MorseRightCapBounds
import ContinuousFlexibility.Radial.MorseLeftCapIntegrals

/-!
# The actual Morse coefficient in the transition-core energy estimate

The negative component of a retained Morse cell has one maximum, at
`log 2`.  Applying the logarithmic energy estimate to this coefficient
gives a two-direction estimate between its actual turning points.  The
positive-cap coefficient products are estimated on the actual retained
intervals, before making a change to the physical radius.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory

private theorem exp_neg_log_two : exp (-log (2 : ℝ)) = 1 / 2 := by
  rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem outer_exp_two (x : ℝ) : exp (-2 * x) = exp (-x) ^ 2 := by
  rw [show -2 * x = -x + -x by ring, exp_add, pow_two]

theorem morseRho_at_peak (A B : ℝ) : morseRho A B (log 2) = A / 4 - B := by
  rw [morseRho, outer_exp_two, exp_neg_log_two]
  ring

theorem morseRho_le_peak {A : ℝ} (hA : 0 ≤ A) (B x : ℝ) :
    morseRho A B x ≤ A / 4 - B := by
  have h := mul_nonneg hA (sq_nonneg (exp (-x) - 1 / 2))
  unfold morseRho
  rw [outer_exp_two]
  nlinarith only [h]

theorem morseRho_monotoneOn_left {A B : ℝ} (hA : 0 ≤ A) :
    MonotoneOn (morseRho A B) (Iic (log 2)) := by
  intro x hx y hy hxy
  have hxy' : exp (-y) ≤ exp (-x) := exp_le_exp.mpr (neg_le_neg hxy)
  have hhalf : 1 / 2 ≤ exp (-y) := by
    rw [← exp_neg_log_two]
    exact exp_le_exp.mpr (neg_le_neg hy)
  have hprod := mul_nonneg (sub_nonneg.mpr hxy')
    (show 0 ≤ exp (-x) + exp (-y) - 1 by linarith)
  have hpoly : exp (-x) - exp (-x) ^ 2 ≤ exp (-y) - exp (-y) ^ 2 := by
    nlinarith only [hprod]
  unfold morseRho
  simp only [outer_exp_two]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hpoly hA) B

theorem morseRho_antitoneOn_right {A B : ℝ} (hA : 0 ≤ A) :
    AntitoneOn (morseRho A B) (Ici (log 2)) := by
  intro x hx y hy hxy
  have hxy' : exp (-y) ≤ exp (-x) := exp_le_exp.mpr (neg_le_neg hxy)
  have hhalf : exp (-x) ≤ 1 / 2 := by
    rw [← exp_neg_log_two]
    exact exp_le_exp.mpr (neg_le_neg hx)
  have hprod := mul_nonneg (sub_nonneg.mpr hxy')
    (show 0 ≤ 1 - exp (-x) - exp (-y) by linarith)
  have hpoly : exp (-y) - exp (-y) ^ 2 ≤ exp (-x) - exp (-x) ^ 2 := by
    nlinarith only [hprod]
  unfold morseRho
  simp only [outer_exp_two]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hpoly hA) B

theorem morse_peak_between_turns {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    log 2 ∈ Ioo (morseLeftTurn A B) (morseRightTurn A B) := by
  have hb := morseRootT_bounds hB hAB
  have hl : exp (-log (2 : ℝ)) < exp (-morseLeftTurn A B) := by
    rw [exp_neg_log_two, exp_neg_morseLeftTurn hB hAB]
    exact hb.2.2.1
  have hr : exp (-morseRightTurn A B) < exp (-log (2 : ℝ)) := by
    rw [exp_neg_log_two, exp_neg_morseRightTurn hB hAB]
    exact hb.2.1
  exact ⟨by linarith only [exp_lt_exp.mp hl], by linarith only [exp_lt_exp.mp hr]⟩

theorem morseRho_nonneg_between_turns {A B : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) {x : ℝ}
    (hx : x ∈ Icc (morseLeftTurn A B) (morseRightTurn A B)) : 0 ≤ morseRho A B x := by
  rcases hx.1.eq_or_lt with h | hl
  · exact le_of_eq ((morseRho_zero_iff_turn hB hAB x).mpr (Or.inl h.symm)).symm
  rcases hx.2.eq_or_lt with h | hr
  · exact le_of_eq ((morseRho_zero_iff_turn hB hAB x).mpr (Or.inr h)).symm
  exact (morseRho_pos_between_turns hB hAB ⟨hl, hr⟩).le

private theorem morseRho_derivative_continuous (A : ℝ) :
    Continuous (fun x : ℝ => A * (exp (-x) * (2 * exp (-x) - 1))) := by
  fun_prop

/-- The logarithmic contribution on the actual negative component. -/
theorem morse_negative_integral_log_le {A B : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) (j : ℝ) :
    (∫ x in morseLeftTurn A B..morseRightTurn A B,
      j ^ 2 * |A * (exp (-x) * (2 * exp (-x) - 1))| /
        (1 + j ^ 2 * morseRho A B x)) ≤ 2 * log (1 + j ^ 2 * (A / 4 - B)) := by
  have hA : 0 ≤ A := ((mul_pos (by norm_num) hB).trans hAB).le
  have hp := morse_peak_between_turns hB hAB
  simpa only [morseRho_at_peak] using
    (negative_integral_log_le (j := j)
      (fun x _ => hasDerivAt_morseRho A B x)
      (fun _ hx => morseRho_nonneg_between_turns hB hAB hx)
      (morseRho_derivative_continuous A).continuousOn ⟨hp.1.le, hp.2.le⟩
      (fun _ hx _ hy hxy => morseRho_monotoneOn_left hA hx.2 hy.2 hxy)
      (fun _ hx _ hy hxy => morseRho_antitoneOn_right hA hx.1 hy.1 hxy))

/-- Both directions have the same bound; the turning-point energy is the
ordinary sum of the squared value and the squared model derivative. -/
theorem morse_negative_endpoint_energy {A B j : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) {u v : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (morseLeftTurn A B) (morseRightTurn A B), HasDerivAt u (v x) x)
    (hv : ∀ x ∈ Icc (morseLeftTurn A B) (morseRightTurn A B),
      HasDerivAt v (-(j ^ 2 * morseRho A B x * u x)) x) :
    let l := morseLeftTurn A B
    let r := morseRightTurn A B
    let K := exp (r - l + 2 * log (1 + j ^ 2 * (A / 4 - B)))
    (v r ^ 2 + u r ^ 2 ≤ (v l ^ 2 + u l ^ 2) * K) ∧
      (v l ^ 2 + u l ^ 2 ≤ (v r ^ 2 + u r ^ 2) * K) := by
  let l := morseLeftTurn A B
  let r := morseRightTurn A B
  let q : ℝ → ℝ := fun x => j ^ 2 * |A * (exp (-x) * (2 * exp (-x) - 1))| /
    (1 + j ^ 2 * morseRho A B x)
  have hlr : l ≤ r := (morseTurn_order hB hAB).le
  have hρ₀ : ∀ x ∈ Icc l r, 0 ≤ morseRho A B x :=
    fun _ hx => morseRho_nonneg_between_turns hB hAB hx
  have hqc : ContinuousOn q (Icc l r) :=
    continuousOn_ratio
      (continuousOn_of_hasDerivAt' (fun x _ => hasDerivAt_morseRho A B x)) hρ₀
      (continuous_abs.comp_continuousOn (morseRho_derivative_continuous A).continuousOn)
  have hq₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ q x := by
    exact div_nonneg (mul_nonneg (sq_nonneg j) (abs_nonneg _))
      (add_nonneg zero_le_one (mul_nonneg (sq_nonneg j) (hρ₀ x hx)))
  have hI₀ : 0 ≤ ∫ x in l..r, 1 + q x :=
    intervalIntegral.integral_nonneg hlr (fun x hx => add_nonneg zero_le_one (hq₀ x hx))
  have hI : |∫ x in l..r, 1 + q x| ≤
      r - l + 2 * log (1 + j ^ 2 * (A / 4 - B)) := by
    rw [abs_of_nonneg hI₀, intervalIntegral.integral_add
      (continuous_const.intervalIntegrable l r) (hqc.intervalIntegrable_of_Icc hlr),
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact add_le_add le_rfl (morse_negative_integral_log_le hB hAB j)
  have hleft : morseRho A B l = 0 :=
    (morseRho_zero_iff_turn hB hAB l).mpr (Or.inl rfl)
  have hright : morseRho A B r = 0 :=
    (morseRho_zero_iff_turn hB hAB r).mpr (Or.inr rfl)
  have htransfer (s t : ℝ) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :=
    negative_energy_transfer hlr hu hv (fun x _ => hasDerivAt_morseRho A B x)
      hρ₀ (morseRho_derivative_continuous A).continuousOn hs ht
  constructor
  · have h := htransfer l r ⟨le_rfl, hlr⟩ ⟨hlr, le_rfl⟩
    simp only [hleft, hright, mul_zero, add_zero, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hI)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  · have h := htransfer r l ⟨hlr, le_rfl⟩ ⟨le_rfl, hlr⟩
    simp only [hleft, hright, mul_zero, add_zero, one_mul] at h
    rw [intervalIntegral.integral_symm l r, abs_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hI)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- On the long cap, its length times the coefficient integral is bounded
by `c² A`.  This is the balanced positive-transfer product in model units. -/
theorem morse_right_cap_balanced_product {A B c : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) (hBA : B ≤ A ^ 9) (hc : 0 ≤ c) :
    (morseRightCapEnd A B c - morseRightTurn A B) *
      (∫ x in morseRightTurn A B..morseRightCapEnd A B c, -morseRho A B x) ≤
        c ^ 2 * A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let l := morseRightTurn A B
  let r := morseRightCapEnd A B c
  have hlength : r - l = c / A ^ 4 := by
    dsimp [l, r, morseRightCapEnd, morseRightCapLength]
    ring
  have hlen₀ : 0 ≤ r - l := by rw [hlength]; positivity
  have hlr : l ≤ r := sub_nonneg.mp hlen₀
  have hρc : Continuous (morseRho A B) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_morseRho A B x).continuousAt
  have hI : (∫ x in l..r, -morseRho A B x) ≤ (r - l) * B := by
    calc
      _ ≤ ∫ _x in l..r, B := intervalIntegral.integral_mono_on hlr
        (hρc.neg.intervalIntegrable l r) (continuous_const.intervalIntegrable l r)
        (fun x hx => (morseRho_right_cap_bounds hB hAB hx.1).2)
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]
  calc
    _ ≤ (r - l) * ((r - l) * B) := mul_le_mul_of_nonneg_left hI hlen₀
    _ ≤ (r - l) * ((r - l) * A ^ 9) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBA hlen₀) hlen₀
    _ = c ^ 2 * A := by rw [hlength]; field_simp [hA.ne']

/-- The short left cap has uniformly bounded model length and a coefficient
of size `A`, so it has the same cap-action scale as the long cap. -/
theorem morse_left_cap_balanced_product {A B : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) :
    (morseLeftTurn A B - morseCellLeftCut) *
      (∫ x in morseCellLeftCut..morseLeftTurn A B, -morseRho A B x) ≤ 12 * A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let l := morseCellLeftCut
  let r := morseLeftTurn A B
  have hl₀ : l < 0 := neg_neg_of_pos (log_pos (by norm_num))
  have hr₀ : 0 < r := by
    exact neg_pos.mpr (log_neg
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (morseRootT_bounds hB hAB).2.2.1)
      (morseRootT_bounds hB hAB).2.2.2)
  have hlr : l ≤ r := (hl₀.trans hr₀).le
  have hlen₀ : 0 ≤ r - l := sub_nonneg.mpr hlr
  have hlen : r - l ≤ 2 := by
    have hp := (morse_peak_between_turns hB hAB).1
    have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have h3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    dsimp only [r, l, morseCellLeftCut]
    linarith only [hp, h2, h3]
  have hρ (x : ℝ) (hx : x ∈ Icc l r) : -morseRho A B x ≤ 3 * A := by
    have he : exp (-x) ≤ 3 / 2 := by
      rw [← exp_neg_morseCellLeftCut]
      exact exp_le_exp.mpr (neg_le_neg hx.1)
    have he₂ : exp (-x) ^ 2 ≤ (3 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (exp_pos _).le he 2
    have hupper := mul_le_mul_of_nonneg_left he₂ hA.le
    have hpositive := mul_nonneg hA.le (exp_pos (-x)).le
    unfold morseRho
    rw [outer_exp_two]
    nlinarith only [hupper, hpositive, hAB, hA]
  have hρc : Continuous (morseRho A B) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_morseRho A B x).continuousAt
  have hI : (∫ x in l..r, -morseRho A B x) ≤ (r - l) * (3 * A) := by
    calc
      _ ≤ ∫ _x in l..r, 3 * A := intervalIntegral.integral_mono_on hlr
        (hρc.neg.intervalIntegrable l r) (continuous_const.intervalIntegrable l r) hρ
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]
  calc
    _ ≤ (r - l) * ((r - l) * (3 * A)) := mul_le_mul_of_nonneg_left hI hlen₀
    _ = (r - l) ^ 2 * (3 * A) := by ring
    _ ≤ 2 ^ 2 * (3 * A) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hlen₀ hlen 2) (by positivity)
    _ = 12 * A := by ring

end ContinuousFlexibility.Radial
