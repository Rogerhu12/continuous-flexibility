import ContinuousFlexibility.Analysis.MorseOpticalComponentLower
import ContinuousFlexibility.Radial.MorseLeftCapBounds

/-!
# Uniform optical lower coefficients for the same realized Morse chain

The actual radius is normalized by its own positive right-root value.
The ODE bound then gives speed at most `7 * D.b * A`. The amplitude is
absent from the optical density, and the inverse coefficient costs only
the sixth power of the model radial envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

def morseRealizationOpticalLower (T : MorseChainData) (D : ReferenceData) (n : ℕ) : ℝ :=
  morseChainB T n / (4 * (7 * D.b * morseChainA T n) ^ 3)

private theorem realized_turn_speed_upper
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) (h100 : 100 ≤ n) :
    8 * morseChainB T n ≤ morseChainA T n ∧
      ∀ x ∈ Icc (morseLeftTurn (morseChainA T n) (morseChainB T n))
          (morseRightTurn (morseChainA T n) (morseChainB T n)),
        deriv (T.radius side n) x ≤ 7 * D.b * morseChainA T n := by
  let A := morseChainA T n
  let B := morseChainB T n
  let R := T.radius side n
  let b := morseRightTurn A B
  let s := R b
  obtain ⟨hB, hAB, hleft, hab, hbe, hright, hspeed⟩ := h.retained_data side n hn
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hd1 : 1 ≤ (T.d n : ℝ) :=
    (one_le_exp_iff.mpr (sq_nonneg (n : ℝ))).trans (h.1 n hn).1
  have hBA := morseChainB_A_bounds T n hd1
  have hA₀ : A ≤ 1 / 1000 := by
    apply morseChainA_le_of_sq_ge_log T n (h.d_eq n hn) (by norm_num)
    have hnR : (100 : ℝ) ≤ n := by exact_mod_cast h100
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hnR 2
    have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9 / (1 / 1000 : ℝ))
    norm_num at hsq hlog ⊢
    linarith only [hlog, hsq]
  have hsmall : 8 * B ≤ A := by
    have hp : A ^ 8 ≤ (1 / 2 : ℝ) ^ 8 :=
      pow_le_pow_left₀ hA.le (hA₀.trans (by norm_num)) 8
    have h8 : 8 * A ^ 8 ≤ 1 := by norm_num at hp; linarith only [hp]
    calc
      _ ≤ 8 * A ^ 9 := mul_le_mul_of_nonneg_left hBA.2 (by norm_num)
      _ = A * (8 * A ^ 8) := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left h8 hA.le
      _ = A := mul_one _
  have hs : 0 < s := h.radius_positive side n hn _ ⟨hab.le, hbe.le⟩
  have hsb : s ≤ D.b := (h.radius_mem_core side n hn _ ⟨hab.le, hbe.le⟩).2.le
  have hR : ContDiff ℝ ∞ R := h.radius_smooth side n hn
  let r : ℝ → ℝ := fun x => R x / s
  have hr : ContDiff ℝ ∞ r := hR.div_const s
  have hd (x : ℝ) : deriv r x = deriv R x / s :=
    ((hR.differentiable (by simp) x).hasDerivAt.div_const s).deriv
  have hdd (x : ℝ) : deriv (deriv r) x = deriv (deriv R) x / s := by
    rw [show deriv r = fun y => deriv R y / s from funext hd]
    exact (((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) x).hasDerivAt.div_const s).deriv
  have hrb : r b = 1 := by dsimp only [r, s]; exact div_self hs.ne'
  have hvb : deriv r b = (1 / 100 : ℝ) * A ^ 5 := by
    rw [hd]
    change deriv (T.radius side n) (morseChainRightTurn T n) / s = _
    rw [hspeed, mul_div_cancel_right₀ _ hs.ne']
  have hsub (x : ℝ) (hx : x ∈ Icc morseCellLeftCut b) :
      x ∈ Icc (T.leftX side n) (T.rightX side n) := by
    rw [hleft]
    exact ⟨hx.1, hx.2.trans hbe.le⟩
  have heq (x : ℝ) (hx : x ∈ Icc morseCellLeftCut b) :
      deriv (deriv r) x = -morseRho A B x * r x := by
    rw [hdd, h.equation side n hn x (hsub x hx)]
    dsimp only [r]
    ring
  have hmodel := (morseLeftCap_radius_bounds hB hAB hA₀ hBA.1 hBA.2
    hr hrb hvb heq).1
  refine ⟨hsmall, ?_⟩
  intro x hx
  have hx' : x ∈ Icc morseCellLeftCut b :=
    ⟨(morseCellLeftCut_lt_shortLeftCapCut.trans
      (morseShortLeftCapCut_lt_leftTurn hB hAB)).le.trans hx.1, hx.2⟩
  have hu : deriv R x ≤ (7 * A) * s :=
    (div_le_iff₀ hs).mp (by rw [← hd]; exact (hmodel x hx').2.2.2.2)
  calc
    deriv R x ≤ (7 * A) * s := hu
    _ ≤ (7 * A) * D.b := mul_le_mul_of_nonneg_left hsb (by positivity)
    _ = 7 * D.b * A := by ring

/-- The constant is chosen before the side and model index and applies
to the actual realized profile, with no additional optical hypothesis. -/
theorem morseRealization_uniform_optical_envelope
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (hstart : 100 ≤ T.index) :
    ∃ K : ℝ, 0 < K ∧ ∀ side n, T.index ≤ n →
      0 < morseRealizationOpticalLower T D n ∧
      (morseRealizationOpticalLower T D n)⁻¹ ≤ K * radialE n ^ (6 : ℝ) ∧
      ∀ r ∈ Ioo
          (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
          (T.radius side n (morseRightTurn (morseChainA T n) (morseChainB T n))),
        morseRealizationOpticalLower T D n *
          min (r - T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
            (T.radius side n (morseRightTurn (morseChainA T n) (morseChainB T n)) - r) ≤
          -deriv D.w r / (r * D.w r) := by
  have hb : 0 < D.b := h.geometry.1.trans h.geometry.2.1
  let K := (4 * (7 * D.b) ^ 3 * (9 : ℝ) ^ 3) * (3 : ℝ) ^ 6
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro side n hn
  have hB := (h.retained_data side n hn).1
  have hA : 0 < morseChainA T n :=
    (mul_pos (by norm_num) hB).trans (h.retained_data side n hn).2.1
  have hV : 0 < 7 * D.b * morseChainA T n := by positivity
  have hκ : 0 < morseRealizationOpticalLower T D n :=
    div_pos hB (mul_pos (by norm_num) (pow_pos hV 3))
  obtain ⟨hsmall, hspeed⟩ := realized_turn_speed_upper h side hn (hstart.trans hn)
  refine ⟨hκ, ?_, morseRealization_optical_lower_of_speed_bound h hσ side hn hsmall hV hspeed⟩
  let d : ℝ := T.d n
  have hd1 : 1 ≤ d :=
    (one_le_exp_iff.mpr (sq_nonneg (n : ℝ))).trans (h.1 n hn).1
  have hd : 0 < d := zero_lt_one.trans_le hd1
  have hA3 := pow_le_pow_left₀ hA.le (morseChainA_inv_bounds T n hd1).2 3
  have hdup : d ≤ 3 * radialE n := by
    have hlt : d < exp ((n : ℝ) ^ 2) + 2 := by
      dsimp only [d]
      rw [h.d_eq n hn]
      exact morseChainInteger_lt n
    have hone : 1 ≤ exp ((n : ℝ) ^ 2) := one_le_exp_iff.mpr (sq_nonneg _)
    have he : exp ((n : ℝ) ^ 2) ≤ radialE n := exp_le_exp.mpr (radial_nat_sq_le_Q n)
    linarith only [hlt, hone, he]
  calc
    (morseRealizationOpticalLower T D n)⁻¹ =
        (4 * (7 * D.b) ^ 3 * d ^ 9) * (morseChainA T n) ^ 3 := by
      rw [morseRealizationOpticalLower, inv_div, div_eq_mul_inv,
        morseChainB_inv_pow T n hd.le, inv_pow, inv_inv]
      ring
    _ ≤ (4 * (7 * D.b) ^ 3 * d ^ 9) * (9 * d⁻¹) ^ 3 :=
      mul_le_mul_of_nonneg_left hA3 (by positivity)
    _ = (4 * (7 * D.b) ^ 3 * (9 : ℝ) ^ 3) * d ^ 6 := by
      field_simp [hd.ne']
      ring
    _ ≤ (4 * (7 * D.b) ^ 3 * (9 : ℝ) ^ 3) * (3 * radialE n) ^ 6 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hdup 6) (by positivity)
    _ = K * radialE n ^ (6 : ℝ) := by rw [mul_pow, Real.rpow_natCast]; dsimp only [K]; ring

end ContinuousFlexibility.Radial
