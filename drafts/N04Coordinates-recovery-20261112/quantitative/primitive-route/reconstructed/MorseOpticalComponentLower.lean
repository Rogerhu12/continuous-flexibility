import ContinuousFlexibility.Radial.MorseModelReturn
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Explicit optical lower bounds on actual Morse components

The two exponential root factors control distance to the nearer root.
The physical change of radius costs three powers of its upper speed.
This is a reconstruction after loss of the original scratch source.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

private theorem exp_sub_lower (u v : ℝ) :
    exp v * (u - v) ≤ exp u - exp v := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u - v)) (exp_pos v).le
  have he : exp v * exp (u - v) = exp u := by rw [← exp_add]; congr 1; ring
  rw [he] at h
  nlinarith only [h]

/-- The coefficient is independent of the actual height amplitude. -/
theorem morseRho_min_distance_lower {A B x : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hsmall : 8 * B ≤ A)
    (hx : x ∈ Icc (morseLeftTurn A B) (morseRightTurn A B)) :
    B / 4 * min (x - morseLeftTurn A B) (morseRightTurn A B - x) ≤
      morseRho A B x := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let p := morseRightRootT A B
  let q := morseLeftRootT A B
  let t := exp (-x)
  have hp : 0 < p := (morseRootT_bounds hB hAB).1
  have hpq : (1 / 2 : ℝ) ≤ q - p := by
    have hratio : 4 * B / A ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ hA).mpr (by nlinarith only [hsmall])
    have hdisc : 0 ≤ 1 - 4 * B / A := by linarith only [hratio]
    have hs : (1 / 2 : ℝ) ≤ sqrt (1 - 4 * B / A) := by
      have hs2 := sq_sqrt hdisc
      nlinarith only [hs2, sqrt_nonneg (1 - 4 * B / A), hratio]
    dsimp only [q, p, morseLeftRootT, morseRightRootT]
    linarith only [hs]
  have hpt : p ≤ t := by
    rw [← exp_neg_morseRightTurn hB hAB]
    exact exp_le_exp.mpr (neg_le_neg hx.2)
  have htq : t ≤ q := by
    rw [← exp_neg_morseLeftTurn hB hAB]
    exact exp_le_exp.mpr (neg_le_neg hx.1)
  let d := min (x - morseLeftTurn A B) (morseRightTurn A B - x)
  have hd : 0 ≤ d := le_min (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
  have hleft : p * d ≤ q - t := by
    have he := exp_sub_lower (-morseLeftTurn A B) (-x)
    rw [exp_neg_morseLeftTurn hB hAB] at he
    change t * (-morseLeftTurn A B - -x) ≤ q - t at he
    have hpd := mul_le_mul_of_nonneg_left (min_le_left _ _) hp.le
    have hptd := mul_le_mul_of_nonneg_right hpt (sub_nonneg.mpr hx.1)
    nlinarith only [hpd, hptd, he]
  have hright : p * d ≤ t - p := by
    have he := exp_sub_lower (-x) (-morseRightTurn A B)
    rw [exp_neg_morseRightTurn hB hAB] at he
    change p * (-x - -morseRightTurn A B) ≤ t - p at he
    have hpd := mul_le_mul_of_nonneg_left (min_le_right _ _) hp.le
    nlinarith only [hpd, he]
  have hprod : p * d / 4 ≤ (t - p) * (q - t) := by
    by_cases ht : (1 / 4 : ℝ) ≤ t - p
    · have hm := mul_le_mul hleft ht (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (sub_nonneg.mpr htq)
      nlinarith only [hm]
    · have hqt : (1 / 4 : ℝ) ≤ q - t := by linarith only [hpq, lt_of_not_ge ht]
      have hm := mul_le_mul hright hqt (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (sub_nonneg.mpr hpt)
      nlinarith only [hm]
  have hBp : B ≤ A * p := by
    have hb := (morseRightRootT_ratio_bounds hB hAB).1
    exact (div_le_iff₀ hA).mp hb |>.trans_eq (mul_comm _ _)
  rw [morseRho_factor hB hAB]
  have hmul := mul_le_mul_of_nonneg_left hprod hA.le
  have hbd := mul_le_mul_of_nonneg_right hBp hd
  change B / 4 * d ≤ A * (t - p) * (q - t)
  nlinarith only [hmul, hbd]

/-- An actual upper bound for the radius speed transfers the two endpoint
distances and the squared density denominator with a cubic cost. -/
theorem optical_min_lower_of_radius_pullback
    {a b V k x ρ : ℝ} {R : ℝ → ℝ}
    (hab : a < b) (hR : ContDiff ℝ ∞ R) (hV : 0 < V) (hk : 0 ≤ k)
    (hv : ∀ t ∈ Icc a b, 0 < deriv R t)
    (hbound : ∀ t ∈ Icc a b, deriv R t ≤ V)
    (hx : x ∈ Icc a b) (hρ : k * min (x - a) (b - x) ≤ ρ) :
    k / V ^ 3 * min (R x - R a) (R b - R x) ≤ ρ / (deriv R x) ^ 2 := by
  have hlip (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) :
      |R t - R s| ≤ V * |t - s| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
        (fun t _ => hR.differentiable (by simp) t)
        (fun t ht => by simpa only [Real.norm_eq_abs, abs_of_pos (hv t ht)]
          using hbound t ht) hs ht
  have hl : R x - R a ≤ V * (x - a) :=
    (le_abs_self _).trans (by simpa only [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      using hlip a (left_mem_Icc.mpr hab.le) x hx)
  have hr : R b - R x ≤ V * (b - x) :=
    (le_abs_self _).trans (by simpa only [abs_of_nonneg (sub_nonneg.mpr hx.2)]
      using hlip x hx b (right_mem_Icc.mpr hab.le))
  have hm : min (R x - R a) (R b - R x) ≤ V * min (x - a) (b - x) := by
    by_cases hs : x - a ≤ b - x
    · rw [min_eq_left hs]
      exact (min_le_left _ _).trans hl
    · rw [min_eq_right (le_of_not_ge hs)]
      exact (min_le_right _ _).trans hr
  have hρ0 : 0 ≤ ρ := (mul_nonneg hk
    (le_min (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))).trans hρ
  calc
    _ ≤ (k / V ^ 3) * (V * min (x - a) (b - x)) :=
      mul_le_mul_of_nonneg_left hm (div_nonneg hk (pow_nonneg hV.le _))
    _ = (k * min (x - a) (b - x)) / V ^ 2 := by field_simp [hV.ne']; ring
    _ ≤ ρ / V ^ 2 := div_le_div_of_nonneg_right hρ (sq_nonneg V)
    _ ≤ ρ / (deriv R x) ^ 2 := div_le_div_of_nonneg_left hρ0
      (pow_pos (hv x hx) 2) (pow_le_pow_left₀ (hv x hx).le (hbound x hx) 2)

/-- The realized profile identity supplies the density; the only numerical
input is an upper speed bound for its actual radius chart. -/
theorem morseRealization_optical_lower_of_speed_bound
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {n : ℕ} (hn : T.index ≤ n)
    (hsmall : 8 * morseChainB T n ≤ morseChainA T n)
    {V : ℝ} (hV : 0 < V)
    (hbound : ∀ x ∈ Icc (morseLeftTurn (morseChainA T n) (morseChainB T n))
        (morseRightTurn (morseChainA T n) (morseChainB T n)),
      deriv (T.radius side n) x ≤ V) :
    ∀ r ∈ Ioo
        (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
        (T.radius side n (morseRightTurn (morseChainA T n) (morseChainB T n))),
      morseChainB T n / (4 * V ^ 3) *
        min (r - T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
          (T.radius side n (morseRightTurn (morseChainA T n) (morseChainB T n)) - r) ≤
        -deriv D.w r / (r * D.w r) := by
  let A := morseChainA T n
  let B := morseChainB T n
  let R := T.radius side n
  let a := morseLeftTurn A B
  let b := morseRightTurn A B
  obtain ⟨hleft, hab, hright⟩ := morseRealization_turns_retained hreal side hn
  have hsub : Icc a b ⊆ Icc (T.leftX side n) (T.rightX side n) :=
    Icc_subset_Icc hleft.le hright.le
  have hR := hreal.radius_smooth side n hn
  have hmono := (hreal.radius_strictMonoOn side n hn).mono hsub
  have himage : R '' Ioo a b = Ioo (R a) (R b) :=
    hR.continuous.continuousOn.image_Ioo_of_strictMonoOn hab.le hmono
  have hdata := hreal.retained_data side n hn
  have hamp := morseChainAmplitude_pos T σ hσ n
  intro r hr
  have hrim : r ∈ R '' Ioo a b := by rw [himage]; exact hr
  obtain ⟨x, hx, rfl⟩ := hrim
  have hx' := hsub (Ioo_subset_Icc_self hx)
  have hrad : R x ≠ 0 := (hreal.radius_positive side n hn x hx').ne'
  have hv : deriv R x ≠ 0 := (hreal.derivative_positive side n hn x hx').ne'
  have hw : D.w (R x) = morseChainAmplitude T σ n * deriv R x :=
    hreal.profile_eq side n hn x hx'
  have hd : deriv D.w (R x) * deriv R x =
      morseChainAmplitude T σ n * (-morseRho A B x * R x) :=
    morseRealization_profile_deriv_scaled hreal side hn hx'
  have hdv := congrArg (fun z : ℝ => z * deriv R x) hd
  have hdensity : -deriv D.w (R x) / (R x * D.w (R x)) =
      morseRho A B x / (deriv R x) ^ 2 := by
    rw [hw]
    field_simp [hamp.ne', hrad, hv] <;> nlinarith only [hd, hdv]
  rw [hdensity]
  have h := optical_min_lower_of_radius_pullback hab hR hV
    (div_nonneg hdata.1.le (by norm_num : (0 : ℝ) ≤ 4))
    (fun t ht => hreal.derivative_positive side n hn t (hsub ht)) hbound
    (Ioo_subset_Icc_self hx)
    (morseRho_min_distance_lower hdata.1 hdata.2.1 hsmall (Ioo_subset_Icc_self hx))
  simpa only [div_div] using h

end ContinuousFlexibility.Radial
