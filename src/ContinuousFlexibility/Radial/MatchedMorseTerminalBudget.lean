module

public import ContinuousFlexibility.Radial.TerminalMorseRelativeSource
public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# A frequency-independent budget for the true terminal column

The leading cap has its proved 400 / (j A²) cost. The true residual
has the fixed original source exponent. Both are absorbed into a fixed
coefficient exponent while keeping the full signed height exponent.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

def matchedMorseTerminalColumnExponent (bcap : ℝ) : ℝ :=
  41415 + |bcap| + terminalMorsePolynomialExponent 400 2 + terminalMorseRelativeSourceExponent

theorem matchedMorseTerminalColumnExponent_ge_cell (bcap : ℝ) :
    (41414 : ℝ) ≤ matchedMorseTerminalColumnExponent bcap := by
  have hs := terminalMorseRelativeSourceExponent_pos.le
  have hp : 0 ≤ terminalMorsePolynomialExponent 400 2 := by
    unfold terminalMorsePolynomialExponent
    positivity
  unfold matchedMorseTerminalColumnExponent
  have hb := abs_nonneg bcap
  linarith

theorem matchedMorseTerminalColumnExponent_nonneg (bcap : ℝ) :
    0 ≤ matchedMorseTerminalColumnExponent bcap :=
  (by norm_num : (0 : ℝ) ≤ 41414).trans (matchedMorseTerminalColumnExponent_ge_cell bcap)

theorem matchedMorse_terminal_cost_bound
    (T : MorseChainData) (N m n : ℕ) (bcap : ℝ) {j δ attenuation C σ : ℝ}
    (hd : T.d m = morseChainInteger m) (hmn : m ≤ n) (hn : 1 ≤ n)
    (hj : 1 ≤ j) (hδ : δ ≤ 1 / 2) (hatt : 0 ≤ attenuation) (hC : 0 ≤ C) :
    exp (radialS N) * exp (bcap * radialQ n + σ * radialS n) *
      (400 / (j * (morseChainA T m) ^ 2) +
        C * ((radialE n ^ terminalMorseRelativeSourceExponent * sqrt δ) *
          exp (-attenuation))) ≤
      (1 + C) * exp (radialS N) *
        exp (matchedMorseTerminalColumnExponent bcap * radialQ n + σ * radialS n) := by
  let ep := terminalMorsePolynomialExponent 400 2
  let es := terminalMorseRelativeSourceExponent
  have hp : 0 ≤ ep := by dsimp only [ep, terminalMorsePolynomialExponent]; positivity
  have hs : 0 ≤ es := terminalMorseRelativeSourceExponent_pos.le
  have hA : 0 < morseChainA T m :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T m hd).1
  have hjp : 0 < j := zero_lt_one.trans_le hj
  have hlead : 400 / (j * (morseChainA T m) ^ 2) ≤ exp (ep * radialQ n) := by
    have hpoly := terminalMorse_polynomial_le_radialE T (by norm_num : (0 : ℝ) < 400)
      2 m n hd hmn hn
    have hden : (morseChainA T m) ^ 2 ≤ j * (morseChainA T m) ^ 2 := by
      nlinarith only [hj, sq_nonneg (morseChainA T m)]
    calc
      _ ≤ 400 / (morseChainA T m) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hA) hden
      _ ≤ radialE n ^ ep := hpoly
      _ = _ := by rw [radialE, ← exp_mul]; congr 1; ring
  have hsqrt : sqrt δ ≤ 1 :=
    (sqrt_le_left zero_le_one).mpr (by nlinarith only [hδ])
  have hexp : exp (-attenuation) ≤ 1 := by
    simpa only [exp_zero] using exp_le_exp.mpr (neg_nonpos.mpr hatt)
  have hpower : 0 ≤ radialE n ^ es := rpow_nonneg (exp_pos (radialQ n)).le es
  have hsource : (radialE n ^ es * sqrt δ) * exp (-attenuation) ≤ exp (es * radialQ n) := by
    calc
      _ ≤ (radialE n ^ es * 1) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hpower)
          hexp (exp_pos _).le (mul_nonneg hpower zero_le_one)
      _ = _ := by rw [mul_one, mul_one, radialE, ← exp_mul]; congr 1; ring
  have hq := radialQ_nonneg n
  have hpl : ep ≤ ep + es := le_add_of_nonneg_right hs
  have hsl : es ≤ ep + es := le_add_of_nonneg_left hp
  have hpExp := exp_le_exp.mpr (mul_le_mul_of_nonneg_right hpl hq)
  have hsExp := exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsl hq)
  have hsum : 400 / (j * (morseChainA T m) ^ 2) +
      C * ((radialE n ^ es * sqrt δ) * exp (-attenuation)) ≤
        (1 + C) * exp ((ep + es) * radialQ n) := by
    calc
      _ ≤ exp (ep * radialQ n) + C * exp (es * radialQ n) :=
        add_le_add hlead (mul_le_mul_of_nonneg_left hsource hC)
      _ ≤ exp ((ep + es) * radialQ n) + C * exp ((ep + es) * radialQ n) :=
        add_le_add hpExp (mul_le_mul_of_nonneg_left hsExp hC)
      _ = _ := by ring
  have he : bcap + ep + es ≤ matchedMorseTerminalColumnExponent bcap := by
    unfold matchedMorseTerminalColumnExponent
    dsimp only [ep, es]
    linarith only [le_abs_self bcap]
  calc
    _ ≤ exp (radialS N) * exp (bcap * radialQ n + σ * radialS n) *
        ((1 + C) * exp ((ep + es) * radialQ n)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 + C) * exp (radialS N) *
        exp ((bcap + ep + es) * radialQ n + σ * radialS n) := by
      rw [show (bcap + ep + es) * radialQ n + σ * radialS n =
        (bcap * radialQ n + σ * radialS n) + (ep + es) * radialQ n by ring,
        exp_add (bcap * radialQ n + σ * radialS n) ((ep + es) * radialQ n)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (add_le_add (mul_le_mul_of_nonneg_right he hq) le_rfl))
      (by positivity)

end ContinuousFlexibility.Radial
