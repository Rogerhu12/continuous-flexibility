module

public import ContinuousFlexibility.Radial.TerminalMatchingFixedThreshold
public import ContinuousFlexibility.Radial.TerminalMorseRelativeSource
public import ContinuousFlexibility.Radial.TerminalMorseEnergyBudget
public import ContinuousFlexibility.Radial.R07LaterSelection

/-!
# A common terminal threshold for the actual later coefficients

The source and energy exponents and the inner inverse exponent are fixed
before Cstar. After choosing any larger Cstar, one starting index makes
their actual matching error smaller than the selected margin.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

def selectedTerminalCoefficientExponent : ℝ :=
  1 + max terminalMorseEnergyErrorExponent (38 + 2 * terminalMorseRelativeSourceExponent)

theorem selectedTerminalCoefficientExponent_pos : 0 < selectedTerminalCoefficientExponent := by
  have h := (le_max_left terminalMorseEnergyErrorExponent
    (38 + 2 * terminalMorseRelativeSourceExponent))
  have he := terminalMorseEnergyErrorExponent_pos
  unfold selectedTerminalCoefficientExponent
  linarith only [h, he]

def selectedTerminalCstarFloor : ℝ :=
  max 1000 (max 1000000000 (100000000 * (64 * selectedTerminalCoefficientExponent + 16)))

theorem selectedTerminalCstarFloor_large : 1000 ≤ selectedTerminalCstarFloor := le_max_left _ _

theorem selectedTerminal_radialE_ge_two {n : ℕ} (hn : 1 ≤ n) : 2 ≤ radialE n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ := radial_nat_sq_le_Q n
  have he := add_one_le_exp (radialQ n)
  change 2 ≤ exp (radialQ n)
  nlinarith only [hn', hQ, he]

theorem exists_selectedTerminalBudgetStart {Cstar : ℝ}
    (hfloor : selectedTerminalCstarFloor ≤ Cstar) :
    ∃ N : ℕ, 100 ≤ N ∧
      ∀ (T : MorseChainData), (∀ m, T.d m = morseChainInteger m) → N ≤ T.index →
      ∀ n j : ℕ, T.index < n → radialFrequencyBand T Cstar n j →
        1000000000 ≤ terminalMatchingAction T (n - 1) j ∧
        (radialE n ^ terminalMorseEnergyErrorExponent + radialE n ^ (38 : ℝ) *
          (radialE n ^ terminalMorseRelativeSourceExponent) ^ (2 : ℕ)) *
          exp (-(terminalMatchingAction T (n - 1) j / 100000000) -
            terminalMatchingAction T (n - 1) j / 100000000) ≤
          ((r07UniformTolerance Cstar * exp (-(n : ℝ) ^ 2)) / 8) / 16 := by
  have hCstar : 0 < Cstar := (by norm_num : (0 : ℝ) < 1000).trans_le
    (selectedTerminalCstarFloor_large.trans hfloor)
  have hlarge : (1000000000 : ℝ) ≤ Cstar :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hfloor)
  have hscaled : 100000000 * (64 * selectedTerminalCoefficientExponent + 16) ≤ Cstar :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hfloor)
  have hscale : 64 * selectedTerminalCoefficientExponent + 16 ≤
      (1 / 100000000 : ℝ) * Cstar := by linarith only [hscaled]
  obtain ⟨N, hN, hbudget⟩ := terminalMatching_uniform_start_of_threshold
    selectedTerminalCoefficientExponent_pos.le (by norm_num : (0 : ℝ) < 1 / 100000000)
    hCstar hscale hlarge
    (div_pos (r07UniformTolerance_pos hCstar.le) (by norm_num : (0 : ℝ) < 8))
  refine ⟨N, hN, ?_⟩
  intro T hT hNT n j hn hband
  have hm : T.index ≤ n - 1 := by omega
  have hn1 : 1 ≤ n := by omega
  have hnid : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  have hb := hbudget T hT hNT (n - 1) hm j (by simpa only [hnid] using hband)
  refine ⟨hb.1, ?_⟩
  have hsmall := hb.2 (terminalMatchingAction T (n - 1) j)
    (terminalMatchingAction T (n - 1) j) le_rfl le_rfl
  rw [hnid] at hsmall
  have hcoeff := terminalMatching_coefficient_power
    (e := terminalMorseEnergyErrorExponent) (g := 38)
    (p := terminalMorseRelativeSourceExponent) (selectedTerminal_radialE_ge_two hn1)
  calc
    _ ≤ radialE n ^ selectedTerminalCoefficientExponent *
        exp (-(terminalMatchingAction T (n - 1) j / 100000000) -
          terminalMatchingAction T (n - 1) j / 100000000) :=
      mul_le_mul_of_nonneg_right hcoeff (exp_pos _).le
    _ = radialE n ^ selectedTerminalCoefficientExponent *
        exp (-(1 / 100000000 : ℝ) * terminalMatchingAction T (n - 1) j -
          (1 / 100000000 : ℝ) * terminalMatchingAction T (n - 1) j) := by
      congr 2
      ring
    _ ≤ terminalMatchingMargin (r07UniformTolerance Cstar / 8) n / 16 := hsmall.le
    _ = _ := by unfold terminalMatchingMargin; ring

end ContinuousFlexibility.Radial
