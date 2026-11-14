module

public import ContinuousFlexibility.Radial.MorseSecondModeScalarBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform deep inequalities on a realized Morse tail

The physical smallness and separation estimates hold after one finite
discard, simultaneously for both orientations. The proof keeps the
actual integrals and the frozen Morse mass/resistance constants.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

/-- Positivity of the actual Morse amplitude parameter. -/
theorem morseSecondMode_A_pos {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n) :
    0 < morseChainA T n :=
  (by positivity : 0 < exp (-(n : ℝ) ^ 2) / 3).trans_le
    (morseChainA_exp_bounds T n (morseSecondMode_chainInteger hreal hn)).1

/-- A logarithmic upper bound for the mass-cell resistance loss. -/
theorem morseSecondMode_logRatio_bounds {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n) :
    0 ≤ log (morseChainA T n / morseChainB T n) ∧
      log (morseChainA T n / morseChainB T n) ≤ 9 * (n : ℝ) ^ 2 + 26 := by
  have hd := morseSecondMode_chainInteger hreal hn
  have hgeom := hreal.2.1 true n hn
  have hB := hgeom.1
  have hAB := hgeom.2.1
  have hA : 0 < morseChainA T n := by linarith
  have hdpos : 0 < (T.d n : ℝ) := by
    have hd2 := morseChainInteger_ge_two n
    rw [hd]
    exact_mod_cast (show 0 < morseChainInteger n by omega)
  have hdhi : (T.d n : ℝ) ≤ 3 * exp ((n : ℝ) ^ 2) := by
    rw [hd]
    have hh := morseChainInteger_lt n
    have he := one_le_exp_iff.mpr (sq_nonneg (n : ℝ))
    linarith
  have hlogd := log_le_log hdpos hdhi
  rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (exp_ne_zero _), log_exp] at hlogd
  have hlog3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  have hlogA := (abs_le.mp (morseChainA_log_error T n hd)).2
  have hlogB : log (morseChainB T n) = -9 * log (T.d n : ℝ) := by
    unfold morseChainB
    rw [log_rpow hdpos]
  refine ⟨log_nonneg ((le_div_iff₀ hB).mpr (by nlinarith)), ?_⟩
  rw [log_div hA.ne' hB.ne', hlogB]
  nlinarith only [hlogd, hlog3, hlogA, sq_nonneg (n : ℝ)]

/-- The common lower coefficient applies to the same cell and to either
of its neighbors. -/
theorem morseSecondMode_coefficient_lower {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ}
    (hn₁ : 1 ≤ n) (hn : T.index ≤ n) (hm : T.index ≤ m)
    (hnear : m = n ∨ m = n + 1 ∨ n = m + 1) :
    exp (2 * (n : ℝ) ^ 2 -
        (10 * (n : ℝ) ^ (3 / 2 : ℝ) + 4 * (n : ℝ) + 75)) ≤
      (morseChainAmplitude T σ m / morseChainAmplitude T σ n) *
        (morseChainA T m ^ 2 / morseChainA T n ^ 4) := by
  rcases hnear with hsame | hadj
  · subst m
    have hAlog := (abs_le.mp (morseChainA_log_error T n
      (morseSecondMode_chainInteger hreal hn))).2
    have hA := morseSecondMode_A_pos hreal hn
    have hlam := morseChainAmplitude_pos T σ hσ n
    have he : 2 * (n : ℝ) ^ 2 -
        (10 * (n : ℝ) ^ (3 / 2 : ℝ) + 4 * (n : ℝ) + 75) ≤
        log ((morseChainA T n ^ 2)⁻¹) := by
      rw [log_inv, log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hAlog, Real.rpow_nonneg (Nat.cast_nonneg n) (3 / 2 : ℝ),
        Nat.cast_nonneg (α := ℝ) n]
    have h := exp_le_exp.mpr he
    rw [exp_log (by positivity : 0 < (morseChainA T n ^ 2)⁻¹)] at h
    calc
      _ ≤ (morseChainA T n ^ 2)⁻¹ := h
      _ = _ := by field_simp [hlam.ne', hA.ne'] <;> ring
  · exact morseSecondMode_adjacent_coefficient hreal hσ hn₁ hn hm hadj

/-- A fixed finite cutoff absorbs the subquadratic error in the
adjacent coefficient. -/
theorem morseSecondMode_quadratic_error {n : ℕ} (hn : 400 ≤ n) :
    10 * (n : ℝ) ^ (3 / 2 : ℝ) + 4 * (n : ℝ) + 75 ≤ (n : ℝ) ^ 2 := by
  have hnR : (400 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hs : (20 : ℝ) ≤ sqrt n := by
    calc
      _ = sqrt (400 : ℝ) := by
        rw [show (400 : ℝ) = 20 ^ 2 by norm_num, sqrt_sq (by norm_num : (0 : ℝ) ≤ 20)]
      _ ≤ _ := sqrt_le_sqrt hnR
  have hp : (n : ℝ) ^ (3 / 2 : ℝ) * sqrt n = (n : ℝ) ^ 2 := by
    rw [sqrt_eq_rpow, ← Real.rpow_add hn0,
      show (3 / 2 : ℝ) + 1 / 2 = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hmul := mul_le_mul_of_nonneg_left hs
    (Real.rpow_nonneg hn0.le (3 / 2 : ℝ))
  have hsq := mul_le_mul_of_nonneg_right hnR hn0.le
  rw [hp] at hmul
  nlinarith only [hmul, hsq, hnR]

/-- A common elementary envelope for both kinds of small products. -/
def morseSecondModeEnvelope (C : ℝ) (n : ℕ) : ℝ :=
  81 * C ^ 2 * exp (-(n : ℝ)) * (9 * (n : ℝ) ^ 2 + 27)

theorem morseSecondModeEnvelope_tendsto (C : ℝ) :
    Tendsto (morseSecondModeEnvelope C) atTop (𝓝 0) := by
  have h₂ : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * exp (-(n : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp tendsto_natCast_atTop_atTop
  have h₀ : Tendsto (fun n : ℕ => exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_zero, one_mul] using
      (tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp
        (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)
  have heq : morseSecondModeEnvelope C =
      (fun n : ℕ => (81 * C ^ 2) *
        (9 * ((n : ℝ) ^ 2 * exp (-(n : ℝ))) + 27 * exp (-(n : ℝ)))) := by
    funext n
    unfold morseSecondModeEnvelope
    ring
  rw [heq]
  simpa only [mul_zero, add_zero] using
    ((h₂.const_mul 9).add (h₀.const_mul 27)).const_mul (81 * C ^ 2)

theorem morseSecondMode_scale_envelope {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) {n : ℕ}
    (hn₁ : 1 ≤ n) (hn : T.index ≤ n) :
    (C 0) ^ 2 * morseChainA T n ^ 2 ≤ morseSecondModeEnvelope (C 0) n ∧
      (C 0) ^ 2 * morseChainA T n ^ 2 *
        log (morseChainA T n / morseChainB T n) ≤ morseSecondModeEnvelope (C 0) n := by
  have hd := morseSecondMode_chainInteger hreal hn
  have hA := morseSecondMode_A_pos hreal hn
  have hAb := (morseChainA_exp_bounds T n hd).2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  have hAsq : morseChainA T n ^ 2 ≤ 81 * exp (-(n : ℝ)) := by
    calc
      _ ≤ (9 * exp (-(n : ℝ) ^ 2)) ^ 2 := (sq_le_sq₀ hA.le (by positivity)).mpr hAb
      _ = 81 * exp (-2 * (n : ℝ) ^ 2) := by
        rw [show exp (-2 * (n : ℝ) ^ 2) =
            exp (-(n : ℝ) ^ 2) * exp (-(n : ℝ) ^ 2) by
          rw [← exp_add]
          congr 1
          ring]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (by nlinarith only [hnR, sq_nonneg ((n : ℝ) - 1)]))
        (by norm_num)
  obtain ⟨hL0, hL⟩ := morseSecondMode_logRatio_bounds hreal hn
  have hcoef := mul_le_mul_of_nonneg_left hAsq (sq_nonneg (C 0))
  constructor
  · calc
      _ ≤ (C 0) ^ 2 * (81 * exp (-(n : ℝ))) := hcoef
      _ ≤ morseSecondModeEnvelope (C 0) n := by
        unfold morseSecondModeEnvelope
        have h := mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ 9 * (n : ℝ) ^ 2 + 27 by nlinarith only [sq_nonneg (n : ℝ)])
          (show 0 ≤ 81 * (C 0) ^ 2 * exp (-(n : ℝ)) by positivity)
        nlinarith only [h]
  · calc
      _ ≤ ((C 0) ^ 2 * (81 * exp (-(n : ℝ)))) *
          (9 * (n : ℝ) ^ 2 + 26) :=
        mul_le_mul hcoef hL hL0 (by positivity)
      _ ≤ morseSecondModeEnvelope (C 0) n := by
        unfold morseSecondModeEnvelope
        have hp : 0 ≤ 81 * (C 0) ^ 2 * exp (-(n : ℝ)) := by positivity
        nlinarith only [hp]

/-- After one finite discard all physical edges obey the numerical deep
inequalities, including both adjacent mass choices. -/
theorem morseSecondMode_eventually_deep {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hmass : MorseMassResistanceBounds T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) :
    ∃ N : ℕ, T.index < N ∧
      ∀ right : Bool, ∀ n, N ≤ n →
        0 < morseCellMass T D right n ∧
        0 < morseJoinResistance T D right n ∧
        12 * morseCellMass T D right n * morseCellResistance T D right n ≤ 1 / 32 ∧
        12 * morseJoinMass T D right n * morseJoinResistance T D right n ≤ 1 / 32 ∧
        ∀ m, N ≤ m → (m = n ∨ m = n + 1 ∨ n = m + 1) →
          32 ≤ 12 * morseCellMass T D right m * morseJoinResistance T D right n ∧
          morseJoinMass T D right n ≤ (1 / 16) * morseCellMass T D right m := by
  have hC : 0 < C 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hacc⟩ := hreal
    exact hacc.2.2.1 0
  have hevent : ∀ᶠ n : ℕ in atTop,
      400 ≤ n ∧ T.index < n ∧
        morseSecondModeEnvelope (C 0) n < 1 / 384 ∧
        32 * (C 0) ^ 2 ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 400, eventually_gt_atTop T.index,
      (morseSecondModeEnvelope_tendsto (C 0)).eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 384)),
      (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (32 * (C 0) ^ 2))]
      with n hn hi hs hl
    exact ⟨hn, hi, hs, hl⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, (hN N le_rfl).2.1, ?_⟩
  intro right n hn
  obtain ⟨hn400, hnindex, hensmall, hnlarge⟩ := hN n hn
  have hn1 : 1 ≤ n := by omega
  have hsn := morseSecondMode_scalarBounds hreal hmass hσ right hnindex.le hnindex.le
  have henv := morseSecondMode_scale_envelope hreal hn1 hnindex.le
  refine ⟨hsn.1, hsn.2.1, ?_, ?_, ?_⟩
  · have h := hsn.2.2.1.trans henv.2
    nlinarith only [h, hensmall]
  · have h := hsn.2.2.2.1.trans henv.1
    nlinarith only [h, hensmall]
  · intro m hm hnear
    have hmindex := (hN m hm).2.1.le
    have hs := morseSecondMode_scalarBounds hreal hmass hσ right hnindex.le hmindex
    let Q : ℝ := (morseChainAmplitude T σ m / morseChainAmplitude T σ n) *
      (morseChainA T m ^ 2 / morseChainA T n ^ 4)
    have hQ : exp ((n : ℝ) ^ 2) ≤ Q := by
      calc
        _ ≤ exp (2 * (n : ℝ) ^ 2 -
            (10 * (n : ℝ) ^ (3 / 2 : ℝ) + 4 * (n : ℝ) + 75)) := by
          apply exp_le_exp.mpr
          have he := morseSecondMode_quadratic_error hn400
          linarith only [he]
        _ ≤ Q := morseSecondMode_coefficient_lower hreal hσ hn1 hnindex.le hmindex hnear
    have hQpos : 0 < Q := (exp_pos _).trans_le hQ
    have hQ1 : 1 ≤ Q := (one_le_exp_iff.mpr (sq_nonneg (n : ℝ))).trans hQ
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hQlarge : 32 ≤ Q / (C 0) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hC)).mpr
      have he := add_one_le_exp ((n : ℝ) ^ 2)
      nlinarith only [hnlarge, hnR, sq_nonneg ((n : ℝ) - 1), he, hQ]
    constructor
    · have hh := hQlarge.trans hs.2.2.2.2.1
      nlinarith only [hh]
    · have hAn := morseSecondMode_A_pos hreal hnindex.le
      have hAm := morseSecondMode_A_pos hreal hmindex
      have hln := morseChainAmplitude_pos T σ hσ n
      have hlm := morseChainAmplitude_pos T σ hσ m
      have heq : (C 0) ^ 2 *
          (morseChainAmplitude T σ n / morseChainAmplitude T σ m) *
          (morseChainA T n ^ 6 / morseChainA T m ^ 2) =
          ((C 0) ^ 2 * morseChainA T n ^ 2) / Q := by
        dsimp only [Q]
        field_simp [hln.ne', hlm.ne', hAn.ne', hAm.ne']
        <;> ring
      have hsmall : ((C 0) ^ 2 * morseChainA T n ^ 2) / Q ≤ 1 / 16 := by
        calc
          _ ≤ (C 0) ^ 2 * morseChainA T n ^ 2 := by
            apply (div_le_iff₀ hQpos).mpr
            have hh := mul_le_mul_of_nonneg_left hQ1
              (by positivity : 0 ≤ (C 0) ^ 2 * morseChainA T n ^ 2)
            simpa only [mul_one] using hh
          _ ≤ morseSecondModeEnvelope (C 0) n := henv.1
          _ ≤ 1 / 16 := by linarith only [hensmall]
      have hmasspos := (morseSecondMode_scalarBounds hreal hmass hσ right
        hmindex hmindex).1
      have hh := hs.2.2.2.2.2
      rw [heq] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hsmall hmasspos.le)

end ContinuousFlexibility.Radial
