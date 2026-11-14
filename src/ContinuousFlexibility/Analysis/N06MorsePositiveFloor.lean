module

public import ContinuousFlexibility.Analysis.N06MorseRootCurvature

/-!
# A distance lower bound on both actual positive Morse caps

The factorization of the literal Morse coefficient gives one estimate from
either root through its entire exterior cap. In particular the lower bound
does not deteriorate again in the long right cap. This supplies the model
input for the physical positive-component estimate, beyond a local simple
root argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

def n06MorseOuterRoot (A B : ℝ) (right : Bool) : ℝ :=
  if right then morseRightTurn A B else morseLeftTurn A B

def n06MorseOuterPoint (A B : ℝ) (right : Bool) (t : ℝ) : ℝ :=
  n06MorseOuterRoot A B right + (if right then t else -t)

theorem n06_morseOuterRoot_zero {A B : ℝ} (hB : 0 < B) (h4 : 4 * B < A)
    (right : Bool) : morseRho A B (n06MorseOuterRoot A B right) = 0 := by
  apply (morseRho_zero_iff_turn hB h4 _).mpr
  cases right with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

theorem n06_morseOuterPoint_distance (A B : ℝ) (right : Bool) {t : ℝ} (ht : 0 ≤ t) :
    |n06MorseOuterPoint A B right t - n06MorseOuterRoot A B right| = t := by
  cases right <;>
    simp only [n06MorseOuterPoint, Bool.false_eq_true, ↓reduceIte,
      add_sub_cancel_left, abs_neg, abs_of_nonneg ht]

private theorem n06_one_sub_exp_neg_lower {t : ℝ} (ht : 0 ≤ t) :
    min t 1 / 2 ≤ 1 - exp (-t) := by
  let u : ℝ := min t 1
  have hu : 0 ≤ u := le_min ht zero_le_one
  have hu1 : u ≤ 1 := min_le_right _ _
  have hut : u ≤ t := min_le_left _ _
  have hup : 0 < u + 1 := by linarith only [hu]
  have hei : exp (-u) ≤ 1 / (u + 1) := by
    rw [exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le hup (add_one_le_exp u)
  have hfrac : 1 / (u + 1) ≤ 1 - u / 2 := by
    apply (div_le_iff₀ hup).mpr
    nlinarith only [mul_nonneg hu (sub_nonneg.mpr hu1)]
  have hem : exp (-t) ≤ exp (-u) := exp_le_exp.mpr (neg_le_neg hut)
  change u / 2 ≤ 1 - exp (-t)
  linarith only [hem, hei, hfrac]

/-- The true two-root factorization supplies a linear lower bound near
either root and a positive floor throughout the remaining cap. -/
theorem n06_morseRho_positive_cap_distance_lower {A B t : ℝ}
    (hB : 0 < B) (h8 : 8 * B ≤ A) (right : Bool) (ht : 0 ≤ t) :
    B / 4 * min t 1 ≤ -morseRho A B (n06MorseOuterPoint A B right t) := by
  have hA : 0 < A := (mul_pos (by norm_num : (0 : ℝ) < 8) hB).trans_le h8
  have h4 : 4 * B < A := by linarith only [hB, h8]
  let r : ℝ := morseRightRootT A B
  let l : ℝ := morseLeftRootT A B
  let s : ℝ := 1 - exp (-t)
  have hroots := morseRootT_bounds hB h4
  have hr : 0 < r := hroots.1
  have hl : 0 < l := (by norm_num : (0 : ℝ) < 1 / 2).trans hroots.2.2.1
  have hr1 : r ≤ 1 := hroots.2.1.le.trans (by norm_num)
  have hl1 : l ≤ 1 := hroots.2.2.2.le
  have hprod : A * r * l = B := by
    calc
      A * r * l = A * (morseRightRootT A B * morseLeftRootT A B) := by ring
      _ = A * (B / A) := by rw [morseRootT_mul hB h4]
      _ = B := by field_simp [hA.ne']
  have hBr : B ≤ A * r := by
    rw [← hprod]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hl1 (mul_nonneg hA.le hr.le)
  have hBl : B ≤ A * l := by
    calc
      B = A * l * r := by rw [← hprod]; ring
      _ ≤ A * l * 1 := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hA.le hl.le)
      _ = A * l := mul_one _
  have hq : B / A ≤ 1 / 8 := (div_le_iff₀ hA).mpr (by linarith only [h8])
  have hgap : (1 / 2 : ℝ) ≤ l - r := by
    have hs : (1 / 2 : ℝ) ≤ sqrt (1 - 4 * B / A) := by
      apply Real.le_sqrt_of_sq_le
      rw [show 4 * B / A = 4 * (B / A) by ring]
      nlinarith only [hq]
    have he : l - r = sqrt (1 - 4 * B / A) := by
      dsimp only [l, r, morseLeftRootT, morseRightRootT]
      ring
    rwa [he]
  have hsm : 0 ≤ s := sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr ht))
  have hnear : B / 4 * min t 1 ≤ B / 2 * s := by
    have hh := mul_le_mul_of_nonneg_left (n06_one_sub_exp_neg_lower ht) (hB.le : 0 ≤ B)
    dsimp only [s]
    linarith only [hh]
  have hproduct {a u v : ℝ} (ha : B ≤ a) (hu : s ≤ u) (hv : (1 / 2 : ℝ) ≤ v) :
      B / 2 * s ≤ a * u * v := by
    calc
      B / 2 * s = (B * s) * (1 / 2) := by ring
      _ ≤ (a * u) * v := mul_le_mul (mul_le_mul ha hu hsm (hB.le.trans ha)) hv
        (by norm_num) (mul_nonneg (hB.le.trans ha) (hsm.trans hu))
  apply hnear.trans
  cases right with
  | false =>
      change B / 2 * s ≤ -morseRho A B (morseLeftTurn A B - t)
      have he : exp (-(morseLeftTurn A B - t)) = l * exp t := by
        rw [show -(morseLeftTurn A B - t) = -morseLeftTurn A B + t by ring,
          exp_add, exp_neg_morseLeftTurn hB h4]
      have hfirst : s ≤ exp t - 1 := by
        dsimp only [s]
        linarith only [add_one_le_exp t, add_one_le_exp (-t)]
      have hsecond : (1 / 2 : ℝ) ≤ l * exp t - r := by
        have hh : l ≤ l * exp t := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_exp ht) hl.le
        linarith only [hgap, hh]
      have hf : -morseRho A B (morseLeftTurn A B - t) =
          (A * l) * (exp t - 1) * (l * exp t - r) := by
        rw [morseRho_factor hB h4, he]
        change -(A * (l * exp t - r) * (l - l * exp t)) = _
        ring
      rw [hf]
      exact hproduct hBl hfirst hsecond
  | true =>
      change B / 2 * s ≤ -morseRho A B (morseRightTurn A B + t)
      have he : exp (-(morseRightTurn A B + t)) = r * exp (-t) := by
        rw [neg_add, exp_add, exp_neg_morseRightTurn hB h4]
      have hsecond : (1 / 2 : ℝ) ≤ l - r * exp (-t) := by
        have hh : r * exp (-t) ≤ r := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (exp_le_one_iff.mpr (neg_nonpos.mpr ht)) hr.le
        linarith only [hgap, hh]
      have hf : -morseRho A B (morseRightTurn A B + t) =
          (A * r) * s * (l - r * exp (-t)) := by
        rw [morseRho_factor hB h4, he]
        change -(A * (r * exp (-t) - r) * (l - r * exp (-t))) = _
        dsimp only [s]
        ring
      rw [hf]
      exact hproduct hBr le_rfl hsecond

/-- The actual allowed height choices have a uniform upper bound, before
any retained model index is chosen. -/
theorem n06_morseChainAmplitude_le_two
    (T : MorseChainData) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (n : ℕ) :
    morseChainAmplitude T σ n ≤ 2 := by
  have hp : (n : ℝ) ≤ (n : ℝ) ^ (5 / 2 : ℝ) := by
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 : ℝ) ≤ 5 / 2)
  have hlog2 : log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hprod : (n : ℝ) * log 2 ≤ (n : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg n)
  have hb := (morseChainAmplitude_log_bounds T σ hσ n).2
  calc
    morseChainAmplitude T σ n = exp (log (morseChainAmplitude T σ n)) :=
      (exp_log (morseChainAmplitude_pos T σ hσ n)).symm
    _ ≤ exp (log 2) := exp_le_exp.mpr (by linarith only [hb, hp, hprod])
    _ = 2 := exp_log (by norm_num)

end ContinuousFlexibility.Analysis
