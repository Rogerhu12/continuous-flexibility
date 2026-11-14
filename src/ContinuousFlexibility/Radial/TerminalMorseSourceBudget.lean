module

public import ContinuousFlexibility.Radial.TerminalMorseSourceNormalization
public import ContinuousFlexibility.Radial.TerminalMatchingThreshold

/-!
# A fixed coefficient budget for the actual terminal source

The inverse Morse powers in the normalized cutoff calculation are
absorbed by the actual chain scales. The exponent is a fixed number
defined from the universal cutoff jets; it is chosen before the
frequency-band threshold and before the tail index.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff ENNReal

/-- The coefficient exponent for a specified inverse power and a
specified positive constant. -/
def terminalMorsePolynomialExponent (C : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) + |log (C * (3 : ℝ) ^ k)|

theorem terminalMorse_polynomial_le_radialE (T : Statements.MorseChainData)
    {C : ℝ} (hC : 0 < C) (k m n : ℕ)
    (hd : T.d m = morseChainInteger m) (hmn : m ≤ n) (hn : 1 ≤ n) :
    C / (Statements.morseChainA T m) ^ k ≤
      Statements.radialE n ^ terminalMorsePolynomialExponent C k := by
  have hA := (morseChainA_exp_bounds T m hd).1
  have hAlow : 0 < exp (-(m : ℝ) ^ 2) / 3 := by positivity
  have hApow := pow_le_pow_left₀ hAlow.le hA k
  have hP : 0 < C * (3 : ℝ) ^ k := by positivity
  have hq : (m : ℝ) ^ 2 ≤ Statements.radialQ n :=
    (radial_nat_sq_le_Q m).trans (radialQ_monotone hmn)
  have hq₁ : 1 ≤ Statements.radialQ n := by
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact (by nlinarith only [hn'] : (1 : ℝ) ≤ (n : ℝ) ^ 2).trans (radial_nat_sq_le_Q n)
  have hlog : log (C * (3 : ℝ) ^ k) ≤
      |log (C * (3 : ℝ) ^ k)| * Statements.radialQ n := by
    exact (le_abs_self _).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hq₁
        (abs_nonneg (log (C * (3 : ℝ) ^ k))))
  have hkq := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg k)
  have heq : (exp (-(m : ℝ) ^ 2) / 3) ^ k =
      exp (-((k : ℝ) * (m : ℝ) ^ 2)) / (3 : ℝ) ^ k := by
    rw [div_pow, ← exp_nat_mul, mul_neg]
  calc
    _ ≤ C / (exp (-(m : ℝ) ^ 2) / 3) ^ k :=
      div_le_div_of_nonneg_left hC.le (pow_pos hAlow k) hApow
    _ = exp (log (C * (3 : ℝ) ^ k) + (k : ℝ) * (m : ℝ) ^ 2) := by
      rw [heq, exp_add, exp_log hP, exp_neg]
      field_simp [(exp_pos ((k : ℝ) * (m : ℝ) ^ 2)).ne',
        pow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)] <;> ring
    _ ≤ exp (Statements.radialQ n * terminalMorsePolynomialExponent C k) := by
      apply exp_le_exp.mpr
      dsimp only [terminalMorsePolynomialExponent]
      nlinarith only [hlog, hkq]
    _ = _ := by rw [Statements.radialE, exp_mul]

/-- This exponent is fixed by the two chosen smooth-cutoff jet bounds.
It does not depend on a cap, height, frequency, band, or tail index. -/
def terminalMorseSourceBudgetExponent : ℝ :=
  terminalMorsePolynomialExponent terminalMorseSourceBudgetConstant 16

theorem terminalMorseSourceBudgetExponent_pos : 0 < terminalMorseSourceBudgetExponent := by
  unfold terminalMorseSourceBudgetExponent terminalMorsePolynomialExponent
  positivity

theorem terminalMorseCapSourcePrefactor_radialE (T : Statements.MorseChainData)
    (long : Bool) (m n : ℕ) {B j s weightScale lam : ℝ} {r w : ℝ → ℝ}
    (hd : T.d m = morseChainInteger m) (hmn : m ≤ n) (hn : 1 ≤ n)
    (hB : 0 < B) (hAB : 4 * B < Statements.morseChainA T m) (hj : 1 ≤ j)
    (hs : 0 < s) (hscale : 0 < weightScale) (hA₀ : Statements.morseChainA T m ≤ 1 / 1000)
    (hr : IsNormalizedMorseCell (Statements.morseChainA T m) B r)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd (Statements.morseChainA T m) B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hnorm : lam = standInBoundaryScale (j ^ 2)
      (w (s * r (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseCellLeftCut)))
      (s * r (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseCellLeftCut))) :
    terminalMorseCapSourcePrefactor long (Statements.morseChainA T m) B j s weightScale lam r ≤
      Statements.radialE n ^ terminalMorseSourceBudgetExponent :=
  (terminalMorseCapSourcePrefactor_normalized long hB hAB hj hs hscale hA₀ hr hweight hnorm).trans
    (terminalMorse_polynomial_le_radialE T terminalMorseSourceBudgetConstant_pos 16 m n hd hmn hn)

/-- The actual source has the coefficient budget needed by terminal
matching, with the exponent fixed before choosing the band threshold. -/
theorem terminalMorse_cutoff_source_radialE (D : Statements.ReferenceData)
    (T : Statements.MorseChainData) (long : Bool) (m n : ℕ)
    {B j s weightScale lam : ℝ} {r u : ℝ → ℝ}
    (hd : T.d m = morseChainInteger m) (hmn : m ≤ n) (hn : 1 ≤ n)
    (hB : 0 < B) (hAB : 4 * B < Statements.morseChainA T m) (hj : 0 < j) (hs : 0 < s)
    (hscale : 0 < weightScale) (hA₀ : Statements.morseChainA T m ≤ 1 / 1000)
    (hBAlo : (Statements.morseChainA T m) ^ 9 / (9 : ℝ) ^ 9 ≤ B)
    (hBAhi : B ≤ (Statements.morseChainA T m) ^ 9)
    (hr : IsNormalizedMorseCell (Statements.morseChainA T m) B r)
    (hw : ContDiff ℝ ∞ D.w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd (Statements.morseChainA T m) B (1 / 100)),
      D.w (s * r x) = weightScale * (s * deriv r x))
    (hode : ∀ x ∈ Icc (if long then morseRightTurn (Statements.morseChainA T m) B else morseCellLeftCut)
        (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseShortLeftCapCut),
      radialJacobi (j ^ 2) D.w u (s * r x) = 0)
    (hzero : u (s * r (if long then morseRightTurn (Statements.morseChainA T m) B else morseShortLeftCapCut)) = 0)
    (hjoin : u (s * r (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseCellLeftCut)) = 1)
    (hinit : long = true → 0 < deriv u (s * r (morseRightTurn (Statements.morseChainA T m) B)))
    (haction : 1000000000 ≤ j * sqrt (Statements.morseChainA T m))
    (hnorm : lam = standInBoundaryScale (j ^ 2)
      (D.w (s * r (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseCellLeftCut)))
      (s * r (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseCellLeftCut))) :
    MemLp (terminalCapHilbertSource lam D.w
        (terminalMorsePhysicalCutoff long (Statements.morseChainA T m) B s r) u)
      2 (Statements.radialHilbertMeasure D) ∧
    eLpNorm (terminalCapHilbertSource lam D.w
        (terminalMorsePhysicalCutoff long (Statements.morseChainA T m) B s r) u)
      2 (Statements.radialHilbertMeasure D) ≤
      ENNReal.ofReal (Statements.radialE n ^ terminalMorseSourceBudgetExponent *
        exp (-(j * sqrt (Statements.morseChainA T m) / 50000000))) := by
  have hA : 0 < Statements.morseChainA T m := (mul_pos (by norm_num) hB).trans hAB
  have hsqrt : sqrt (Statements.morseChainA T m) ≤ 1 :=
    (sqrt_le_left zero_le_one).mpr (by
      simpa only [one_pow] using hA₀.trans (by norm_num : (1 / 1000 : ℝ) ≤ 1))
  have hj₁ : 1 ≤ j := by
    have h := mul_le_mul_of_nonneg_left hsqrt hj.le
    nlinarith only [h, haction]
  have hlamlo := terminalMorse_boundary_normalization_lower long hB hAB hs hscale hr hweight hnorm
  have hlam : 0 < lam :=
    (by positivity : 0 < j ^ 2 * weightScale * (Statements.morseChainA T m) ^ 5 / 200).trans_le hlamlo
  obtain ⟨hmem, hbound⟩ := terminalMorse_cutoff_source_L2 D long hB hAB hj hs hscale hlam
    hA₀ hBAlo hBAhi hr hw hu hweight hode hzero hjoin hinit haction
  refine ⟨hmem, hbound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact mul_le_mul_of_nonneg_right
    (terminalMorseCapSourcePrefactor_radialE T long m n hd hmn hn hB hAB hj₁ hs hscale hA₀ hr hweight hnorm)
    (exp_pos _).le

end ContinuousFlexibility.Radial

