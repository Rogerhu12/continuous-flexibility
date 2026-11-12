import ContinuousFlexibility.Radial.TerminalMorseSourceBudget
import ContinuousFlexibility.Radial.TerminalMorseBoundarySlopeLower

/-!
# The terminal source relative to the actual stand-in energy

The same incoming solution supplies the positive normalized slope d.
Its secant lower bound loses only a polynomial frequency factor. Half
of the proved cap attenuation absorbs that factor uniformly, leaving
a fixed coefficient exponent chosen before any band threshold.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff ENNReal

theorem terminalCap_absorb_action (t : ℝ) :
    t * exp (-(t / 50000000)) ≤ 100000000 * exp (-(t / 100000000)) := by
  have h := add_one_le_exp (t / 100000000)
  have ht : t ≤ 100000000 * exp (t / 100000000) := by linarith only [h]
  calc
    _ ≤ (100000000 * exp (t / 100000000)) * exp (-(t / 50000000)) :=
      mul_le_mul_of_nonneg_right ht (exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← exp_add]
      congr 1
      ring

/-- The explicit polynomial loss in d is absorbed uniformly at every
frequency by the same half of the cap exponential. -/
theorem terminalCap_relative_attenuation {A j d P C : ℝ}
    (hA : 0 < A) (hA₁ : A ≤ 1) (hj : 0 < j) (hC : 0 < C)
    (hP : P ≤ C / A ^ 16) (hd : A ^ 3 / (14 * j ^ 2) ≤ d) :
    P * exp (-(j * sqrt A / 50000000)) ≤
      sqrt d * (400000000 * C / A ^ 19) * exp (-(j * sqrt A / 100000000)) := by
  have hslope := terminalCap_sqrt_slope_lower hA hA₁ hj hd
  have hweight : 1 ≤ (4 * j / A ^ 2) * sqrt d := by
    calc
      _ = (4 * j / A ^ 2) * (A ^ 2 / (4 * j)) := by
        field_simp [hA.ne', hj.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hslope (by positivity)
  have hpref : P ≤ sqrt d * (4 * C * j / A ^ 18) := by
    calc
      _ ≤ C / A ^ 16 := hP
      _ ≤ (C / A ^ 16) * ((4 * j / A ^ 2) * sqrt d) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ C / A ^ 16)
      _ = _ := by field_simp [hA.ne'] <;> ring
  have hAsqrt : A ≤ sqrt A := by
    apply (sq_le_sq₀ hA.le (sqrt_nonneg A)).mp
    rw [sq_sqrt hA.le]
    nlinarith only [hA, hA₁]
  have hjtau : j ≤ (j * sqrt A) / A :=
    (le_div_iff₀ hA).mpr (mul_le_mul_of_nonneg_left hAsqrt hj.le)
  have hfrequency : 4 * C * j / A ^ 18 ≤ 4 * C * (j * sqrt A) / A ^ 19 := by
    calc
      _ ≤ 4 * C * ((j * sqrt A) / A) / A ^ 18 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hjtau (by positivity)) (by positivity)
      _ = _ := by field_simp [hA.ne'] <;> ring
  calc
    _ ≤ (sqrt d * (4 * C * j / A ^ 18)) * exp (-(j * sqrt A / 50000000)) :=
      mul_le_mul_of_nonneg_right hpref (exp_pos _).le
    _ ≤ (sqrt d * (4 * C * (j * sqrt A) / A ^ 19)) * exp (-(j * sqrt A / 50000000)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfrequency (sqrt_nonneg d)) (exp_pos _).le
    _ = (sqrt d * (4 * C / A ^ 19)) *
        ((j * sqrt A) * exp (-(j * sqrt A / 50000000))) := by ring
    _ ≤ (sqrt d * (4 * C / A ^ 19)) *
        (100000000 * exp (-(j * sqrt A / 100000000))) :=
      mul_le_mul_of_nonneg_left (terminalCap_absorb_action _) (by positivity)
    _ = _ := by ring

def terminalMorseRelativeSourceConstant : ℝ := 400000000 * terminalMorseSourceBudgetConstant

theorem terminalMorseRelativeSourceConstant_pos : 0 < terminalMorseRelativeSourceConstant :=
  mul_pos (by norm_num) terminalMorseSourceBudgetConstant_pos

/-- This exponent is independent of the selected height and of Cstar.
It is therefore available before the terminal threshold is chosen. -/
def terminalMorseRelativeSourceExponent : ℝ :=
  terminalMorsePolynomialExponent terminalMorseRelativeSourceConstant 19

theorem terminalMorseRelativeSourceExponent_pos : 0 < terminalMorseRelativeSourceExponent := by
  unfold terminalMorseRelativeSourceExponent terminalMorsePolynomialExponent
  positivity

/-- The actual cutoff source has the required square-root stand-in
factor. All quantities refer to the very same input incoming solution. -/
theorem terminalMorse_cutoff_source_relative_radialE (D : Statements.ReferenceData)
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
    let d := standInBoundarySlope (if long then 1 else -1) (j ^ 2)
      (s * r (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseCellLeftCut)) u
    MemLp (terminalCapHilbertSource lam D.w
        (terminalMorsePhysicalCutoff long (Statements.morseChainA T m) B s r) u)
      2 (Statements.radialHilbertMeasure D) ∧
    eLpNorm (terminalCapHilbertSource lam D.w
        (terminalMorsePhysicalCutoff long (Statements.morseChainA T m) B s r) u)
      2 (Statements.radialHilbertMeasure D) ≤
      ENNReal.ofReal (sqrt d * Statements.radialE n ^ terminalMorseRelativeSourceExponent *
        exp (-(j * sqrt (Statements.morseChainA T m) / 100000000))) := by
  have hA : 0 < Statements.morseChainA T m := (mul_pos (by norm_num) hB).trans hAB
  have hA₁ : Statements.morseChainA T m ≤ 1 := hA₀.trans (by norm_num)
  have hsqrt : sqrt (Statements.morseChainA T m) ≤ 1 :=
    (sqrt_le_left zero_le_one).mpr (by simpa only [one_pow] using hA₁)
  have hj₁ : 1 ≤ j := by
    have h := mul_le_mul_of_nonneg_left hsqrt hj.le
    nlinarith only [h, haction]
  have hlamlo := terminalMorse_boundary_normalization_lower long hB hAB hs hscale hr hweight hnorm
  have hlam : 0 < lam :=
    (by positivity : 0 < j ^ 2 * weightScale * (Statements.morseChainA T m) ^ 5 / 200).trans_le hlamlo
  obtain ⟨hmem, hnormbound⟩ := terminalMorse_cutoff_source_L2 D long hB hAB hj hs hscale hlam
    hA₀ hBAlo hBAhi hr hw hu hweight hode hzero hjoin hinit haction
  have hslope := terminalMorse_standIn_slope_lower long hB hAB hj hs hscale.ne' hA₀
    hr hw hu hweight hode hzero hjoin
  have hpref := terminalMorseCapSourcePrefactor_normalized long hB hAB hj₁ hs hscale hA₀ hr hweight hnorm
  have hrelative := terminalCap_relative_attenuation hA hA₁ hj terminalMorseSourceBudgetConstant_pos hpref hslope
  have hbudget := terminalMorse_polynomial_le_radialE T terminalMorseRelativeSourceConstant_pos
    19 m n hd hmn hn
  refine ⟨hmem, hnormbound.trans (ENNReal.ofReal_le_ofReal (hrelative.trans ?_))⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbudget (sqrt_nonneg _)) (exp_pos _).le

end ContinuousFlexibility.Radial

