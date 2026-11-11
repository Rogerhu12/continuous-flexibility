import ContinuousFlexibility.Radial.R07IncomingCap
import ContinuousFlexibility.Radial.MorseChainGeometry
import ContinuousFlexibility.Radial.MorseCellMassTravel

/-!
# The concrete Morse caps for normalized incoming solutions

The right cap begins at the right turning point. The left cap begins at
the fixed short-cap cut and is traversed backwards. Both use one affine
coordinate with the outward sign, so the physical dilation cancels from
the Riccati slope estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

def r07CapCut (right : Bool) (A B : ℝ) : ℝ :=
  if right then morseRightTurn A B else morseShortLeftCapCut

def r07CapLength (right : Bool) (A : ℝ) : ℝ :=
  if right then morseRightCapLength A (1 / 100) else morseShortLeftCapLength

def r07CapEnd (right : Bool) (A B : ℝ) : ℝ :=
  if right then morseRightCapEnd A B (1 / 100) else morseCellLeftCut

def r07CapPoint (right : Bool) (A B t : ℝ) : ℝ :=
  r07CapCut right A B + r07OutwardSign right * t

def r07CapRadius (right : Bool) (A B s : ℝ) (r : ℝ → ℝ) : ℝ → ℝ :=
  fun t => s * r (r07CapPoint right A B t)

def r07CapRiccatiBound (right : Bool) (A j : ℝ) : ℝ :=
  if right then j * A ^ 4 * sqrt A else j * sqrt A

theorem r07CapPoint_zero (right : Bool) (A B : ℝ) :
    r07CapPoint right A B 0 = r07CapCut right A B := by simp [r07CapPoint]

theorem r07CapPoint_end (right : Bool) (A B : ℝ) :
    r07CapPoint right A B (r07CapLength right A) = r07CapEnd right A B := by
  cases right <;>
    simp [r07CapPoint, r07CapCut, r07CapLength, r07CapEnd, r07OutwardSign,
      morseShortLeftCapLength, morseRightCapEnd] <;> ring

theorem r07CapLength_pos (right : Bool) {A : ℝ} (hA : 0 < A) : 0 < r07CapLength right A := by
  cases right
  · exact morseShortLeftCapLength_pos
  · exact morseRightCapLength_pos hA (by norm_num)

theorem r07CapRiccatiBound_pos (right : Bool) {A j : ℝ} (hA : 0 < A) (hj : 0 < j) :
    0 < r07CapRiccatiBound right A j := by
  cases right <;> simp only [r07CapRiccatiBound, Bool.false_eq_true, if_false, if_true] <;> positivity

theorem r07CapPoint_mem (right : Bool) {A B t : ℝ}
    (ht : t ∈ Icc 0 (r07CapLength right A)) :
    if right then r07CapPoint right A B t ∈
        Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100))
      else r07CapPoint right A B t ∈ Icc morseCellLeftCut morseShortLeftCapCut := by
  cases right <;>
    simp only [r07CapPoint, r07CapCut, r07CapLength, r07OutwardSign, Bool.false_eq_true,
      if_false, if_true, neg_one_mul, one_mul, mem_Icc, morseShortLeftCapLength,
      morseRightCapEnd] at ht ⊢ <;>
    constructor <;> linarith only [ht.1, ht.2]

theorem r07CapPoint_mem_cell (right : Bool) {A B t : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (ht : t ∈ Icc 0 (r07CapLength right A)) :
    r07CapPoint right A B t ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) := by
  have hm := r07CapPoint_mem (B := B) right ht
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hturn : morseCellLeftCut < morseRightTurn A B := morseCellLeftCut_lt_rightTurn hB hAB
  have hshort : morseShortLeftCapCut < morseRightTurn A B :=
    (morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)
  have he : morseRightTurn A B ≤ morseRightCapEnd A B (1 / 100) :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  cases right
  · exact ⟨hm.1, hm.2.trans (hshort.le.trans he)⟩
  · exact ⟨hturn.le.trans hm.1, hm.2⟩

theorem r07CapRadius_smooth (right : Bool) (A B s : ℝ) {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) : ContDiff ℝ ∞ (r07CapRadius right A B s r) :=
  contDiff_const.mul (hr.comp (contDiff_const.add (contDiff_const.mul contDiff_id)))

theorem r07CapRadius_deriv (right : Bool) (A B s t : ℝ) {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) :
    deriv (r07CapRadius right A B s r) t =
      s * deriv r (r07CapPoint right A B t) * r07OutwardSign right := by
  have hp : HasDerivAt (r07CapPoint right A B) (r07OutwardSign right) t := by
    change HasDerivAt (fun x : ℝ => r07CapCut right A B + r07OutwardSign right * x)
      (r07OutwardSign right) t
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul (r07OutwardSign right)).const_add (r07CapCut right A B)
  have h := ((hr.differentiable (by simp) (r07CapPoint right A B t)).hasDerivAt.comp t hp).const_mul s
  change deriv (fun y : ℝ => s * r (r07CapPoint right A B y)) t = _
  simpa only [Function.comp_apply, mul_assoc] using h.deriv

theorem r07CapRadius_second (right : Bool) (A B s t : ℝ) {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) :
    deriv (deriv (r07CapRadius right A B s r)) t =
      s * deriv (deriv r) (r07CapPoint right A B t) := by
  have hr' : ContDiff ℝ ∞ (deriv r) := (contDiff_infty_iff_deriv.mp hr).2
  have hd : deriv (r07CapRadius right A B s r) =
      fun t => s * deriv r (r07CapPoint right A B t) * r07OutwardSign right :=
    funext (fun t => r07CapRadius_deriv right A B s t hr)
  rw [hd, deriv_mul_const_field]
  change deriv (r07CapRadius right A B s (deriv r)) t * r07OutwardSign right = _
  rw [r07CapRadius_deriv right A B s t hr']
  calc
    _ = s * deriv (deriv r) (r07CapPoint right A B t) * r07OutwardSign right ^ 2 := by ring
    _ = _ := by rw [r07OutwardSign_sq, mul_one]

private theorem r07CapPoint_mem_enlarged (right : Bool) {A B t : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (ht : t ∈ Icc 0 (r07CapLength right A)) :
    r07CapPoint right A B t ∈ Icc (morseCellLeftCut - morseJoinCollarWidth)
      (morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth) := by
  have hm := r07CapPoint_mem_cell right hB hAB ht
  have hc : (0 : ℝ) ≤ morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
  exact ⟨by linarith only [hm.1, hc], by linarith only [hm.2, hc]⟩

theorem r07CapRadius_model_bounds (right : Bool) {A B s t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r)
    (ht : t ∈ Icc 0 (r07CapLength right A)) :
    0 < r07CapRadius right A B s r t ∧
      (if right then 0 < deriv (r07CapRadius right A B s r) t
       else deriv (r07CapRadius right A B s r) t < 0) := by
  have hm := r07CapPoint_mem (B := B) right ht
  have hv := hr.speed_pos _ (r07CapPoint_mem_enlarged right hB hAB ht)
  have hp : 0 < r (r07CapPoint right A B t) := by
    cases right
    · exact (hr.left_half _ ⟨hm.1, hm.2.trans
        ((morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)).le⟩).2.1
    · exact (hr.right_half _ hm).2.1
  refine ⟨mul_pos hs hp, ?_⟩
  rw [r07CapRadius_deriv right A B s t hr.smooth]
  have hmul := mul_pos hs hv
  cases right <;> simpa [r07OutwardSign] using hmul

theorem r07CapRadius_equation (right : Bool) {A B s t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hr : IsNormalizedMorseCell A B r)
    (ht : t ∈ Icc 0 (r07CapLength right A)) :
    deriv (deriv (r07CapRadius right A B s r)) t =
      -morseRho A B (r07CapPoint right A B t) * r07CapRadius right A B s r t := by
  rw [r07CapRadius_second right A B s t hr.smooth,
    hr.equation _ (r07CapPoint_mem_enlarged right hB hAB ht)]
  dsimp only [r07CapRadius]
  ring

theorem r07CapRadius_abs_deriv (right : Bool) {A B s t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r)
    (ht : t ∈ Icc 0 (r07CapLength right A)) :
    |deriv (r07CapRadius right A B s r) t| = s * deriv r (r07CapPoint right A B t) := by
  have hv := hr.speed_pos _ (r07CapPoint_mem_enlarged right hB hAB ht)
  rw [r07CapRadius_deriv right A B s t hr.smooth, abs_mul, abs_of_pos (mul_pos hs hv)]
  have hsign : |r07OutwardSign right| = 1 := by cases right <;> norm_num [r07OutwardSign]
  rw [hsign, mul_one]

/-- The scalar comparison coefficient is the same Morse coefficient for
either orientation; the physical dilation has cancelled. -/
theorem r07CapRadius_scalar_bound (right : Bool) {A B s j t : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hBA : B ≤ A ^ 9) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r) (ht : t ∈ Icc 0 (r07CapLength right A)) :
    0 ≤ j ^ 2 * deriv (deriv (r07CapRadius right A B s r)) t /
      r07CapRadius right A B s r t ∧
    j ^ 2 * deriv (deriv (r07CapRadius right A B s r)) t /
      r07CapRadius right A B s r t ≤ r07CapRiccatiBound right A j ^ 2 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hp := (r07CapRadius_model_bounds right hB hAB hs hr ht).1
  have he : j ^ 2 * deriv (deriv (r07CapRadius right A B s r)) t /
      r07CapRadius right A B s r t = j ^ 2 * (-morseRho A B (r07CapPoint right A B t)) := by
    rw [r07CapRadius_equation right hB hAB hr ht]
    field_simp [hp.ne'] <;> ring
  rw [he]
  have hm := r07CapPoint_mem (B := B) right ht
  cases right
  · have hlo := morseShortLeftCap_negRho_lower hB hAB hm.2
    have hhi := morseLeftCap_negRho_upper hB hAB hm.1
    refine ⟨mul_nonneg (sq_nonneg _) ((div_pos hA (by norm_num)).le.trans hlo), ?_⟩
    calc
      _ ≤ j ^ 2 * A := mul_le_mul_of_nonneg_left hhi (sq_nonneg _)
      _ = _ := by simp [r07CapRiccatiBound, mul_pow, sq_sqrt hA.le]
  · have hρ := morseRho_right_cap_bounds hB hAB hm.1
    refine ⟨mul_nonneg (sq_nonneg _) hρ.1, ?_⟩
    calc
      _ ≤ j ^ 2 * A ^ 9 := mul_le_mul_of_nonneg_left (hρ.2.trans hBA) (sq_nonneg _)
      _ = _ := by simp [r07CapRiccatiBound, mul_pow, sq_sqrt hA.le] <;> ring

theorem r07_short_cap_inverse_length_le : 1 / morseShortLeftCapLength ≤ 6 := by
  have hlog := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6 / 5)
  have hratio : (3 / 2 : ℝ) / (5 / 4) = 6 / 5 := by norm_num
  have hd := log_div (by norm_num : (3 / 2 : ℝ) ≠ 0) (by norm_num : (5 / 4 : ℝ) ≠ 0)
  rw [hratio] at hd
  have hlen : (1 / 6 : ℝ) ≤ morseShortLeftCapLength := by
    unfold morseShortLeftCapLength morseShortLeftCapCut morseCellLeftCut
    norm_num at hlog
    linarith only [hlog, hd]
  exact (div_le_iff₀ morseShortLeftCapLength_pos).mpr (by linarith only [hlen])

theorem r07_large_action_numeric_bound {t : ℝ} (ht : 1000 ≤ t) :
    200 / t + 20000 / t ^ 2 ≤ 1 / 2 := by
  have ht₀ : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hsq : (1000000 : ℝ) ≤ t ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1000) ht 2
    norm_num at h
    exact h
  have hfirst : 200 / t ≤ 1 / 5 := (div_le_iff₀ ht₀).mpr (by linarith only [ht])
  have hsecond : 20000 / t ^ 2 ≤ 1 / 50 :=
    (div_le_iff₀ (sq_pos_of_pos ht₀)).mpr (by linarith only [hsq])
  linarith only [hfirst, hsecond]

private theorem r07_cap_endpoint_ratio_bound {radius speed lower j : ℝ}
    (hR : radius ≤ 2) (hlower : 0 < lower) (hspeed : lower ≤ speed) (hj : 0 < j) :
    radius / (j ^ 2 * speed) ≤ 2 / (j ^ 2 * lower) := by
  have hspeed₀ : 0 < speed := hlower.trans_le hspeed
  calc
    _ ≤ 2 / (j ^ 2 * speed) := div_le_div_of_nonneg_right hR (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hspeed (sq_nonneg _))

/-- A single explicit majorant works for both actual Morse caps. -/
theorem r07_model_cap_slope_bound (right : Bool) {A B j : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hr : IsNormalizedMorseCell A B r) :
    r (r07CapEnd right A B) / (j ^ 2 * deriv r (r07CapEnd right A B)) *
        (r07CapRiccatiBound right A j + 1 / r07CapLength right A) ≤
      200 / (j * sqrt A) + 20000 / (j * sqrt A) ^ 2 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have ha : 0 < sqrt A := sqrt_pos.mpr hA
  have hja : 0 < j * sqrt A := mul_pos hj ha
  have hleft := hr.left_half morseCellLeftCut
    ⟨le_rfl, (morseCellLeftCut_lt_rightTurn hB hAB).le⟩
  have hbe : morseRightTurn A B ≤ morseRightCapEnd A B (1 / 100) :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hright := hr.right_half (morseRightCapEnd A B (1 / 100)) ⟨hbe, le_rfl⟩
  cases right
  · have hratio := r07_cap_endpoint_ratio_bound hleft.2.2.1
      (by positivity : (0 : ℝ) < A / 4) hr.left_speed hj
    have hratio' : r morseCellLeftCut / (j ^ 2 * deriv r morseCellLeftCut) ≤ 8 / (j ^ 2 * A) := by
      calc
        _ ≤ _ := hratio
        _ = _ := by field_simp [hj.ne', hA.ne'] <;> ring
    change r morseCellLeftCut / (j ^ 2 * deriv r morseCellLeftCut) *
      (j * sqrt A + 1 / morseShortLeftCapLength) ≤ _
    calc
      _ ≤ (8 / (j ^ 2 * A)) * (j * sqrt A + 6) :=
        mul_le_mul hratio' (add_le_add le_rfl r07_short_cap_inverse_length_le)
          (add_nonneg hja.le (one_div_pos.mpr morseShortLeftCapLength_pos).le) (by positivity)
      _ = 8 / (j * sqrt A) + 48 / (j * sqrt A) ^ 2 := by
        set a := sqrt A with haDef
        have ha₂ : a ^ 2 = A := sq_sqrt hA.le
        have ha₀ : a ≠ 0 := ha.ne'
        change 8 / (j ^ 2 * A) * (j * a + 6) = 8 / (j * a) + 48 / (j * a) ^ 2
        rw [← ha₂]
        field_simp [hj.ne', ha₀] <;> ring
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_right (by norm_num) hja.le)
        (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _))
  · have hratio := r07_cap_endpoint_ratio_bound hright.2.2.1
      (by positivity : (0 : ℝ) < (1 / 100 : ℝ) * A ^ 5) hright.2.2.2.1 hj
    have hratio' : r (morseRightCapEnd A B (1 / 100)) /
        (j ^ 2 * deriv r (morseRightCapEnd A B (1 / 100))) ≤ 200 / (j ^ 2 * A ^ 5) := by
      calc
        _ ≤ _ := hratio
        _ = _ := by field_simp [hj.ne', hA.ne'] <;> ring
    have hlen : 1 / morseRightCapLength A (1 / 100) = 100 * A ^ 4 := by
      unfold morseRightCapLength
      field_simp [hA.ne'] <;> ring
    change r (morseRightCapEnd A B (1 / 100)) /
      (j ^ 2 * deriv r (morseRightCapEnd A B (1 / 100))) *
      (j * A ^ 4 * sqrt A + 1 / morseRightCapLength A (1 / 100)) ≤ _
    rw [hlen]
    calc
      _ ≤ (200 / (j ^ 2 * A ^ 5)) * (j * A ^ 4 * sqrt A + 100 * A ^ 4) :=
        mul_le_mul_of_nonneg_right hratio' (by positivity)
      _ = _ := by
        set a := sqrt A with haDef
        have ha₂ : a ^ 2 = A := sq_sqrt hA.le
        have ha₀ : a ≠ 0 := ha.ne'
        change 200 / (j ^ 2 * A ^ 5) * (j * A ^ 4 * a + 100 * A ^ 4) =
          200 / (j * a) + 20000 / (j * a) ^ 2
        rw [← ha₂]
        field_simp [hj.ne', ha₀] <;> ring

/-- The concrete comparison bound is at most one half as soon as the
frequency action is at least `1000`, independently of the cell and radius. -/
theorem r07CapRadius_slope_small (right : Bool) {A B s j : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hj : 0 < j)
    (hr : IsNormalizedMorseCell A B r) (haction : 1000 ≤ j * sqrt A) :
    r07CapRadius right A B s r (r07CapLength right A) /
        (j ^ 2 * |deriv (r07CapRadius right A B s r) (r07CapLength right A)|) *
      (r07CapRiccatiBound right A j + 1 / r07CapLength right A) ≤ 1 / 2 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : r07CapLength right A ∈ Icc 0 (r07CapLength right A) :=
    ⟨(r07CapLength_pos right hA).le, le_rfl⟩
  rw [r07CapRadius_abs_deriv right hB hAB hs hr hL]
  change (s * r (r07CapPoint right A B (r07CapLength right A))) /
    (j ^ 2 * (s * deriv r (r07CapPoint right A B (r07CapLength right A)))) * _ ≤ _
  rw [r07CapPoint_end]
  have hratio : (s * r (r07CapEnd right A B)) /
      (j ^ 2 * (s * deriv r (r07CapEnd right A B))) =
      r (r07CapEnd right A B) / (j ^ 2 * deriv r (r07CapEnd right A B)) := by
    rw [show j ^ 2 * (s * deriv r (r07CapEnd right A B)) =
      s * (j ^ 2 * deriv r (r07CapEnd right A B)) by ring]
    exact mul_div_mul_left _ _ hs.ne'
  rw [hratio]
  exact (r07_model_cap_slope_bound right hB hAB hj hr).trans (r07_large_action_numeric_bound haction)

end ContinuousFlexibility.Radial
