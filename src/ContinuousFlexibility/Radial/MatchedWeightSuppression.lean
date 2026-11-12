import ContinuousFlexibility.Radial.InnerUniformSuppression
import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Adjacent-action suppression for returning matched blocks

The inner suppression theorem is reused without changing its construction.
The extra ingredient for a returning block is that the action at the
transition cell is an arbitrarily small multiple of the preceding action.
The existing Morse transition-ratio limit proves this uniformly in frequency.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real
open scoped Topology
open ContinuousFlexibility.Statements

/-- The square-root Morse scale at the next cell is eventually smaller by
any prescribed positive factor. No frequency appears in the chosen index. -/
theorem matched_morse_adjacent_sqrt_small (T : MorseChainData)
    (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      sqrt (morseChainA T (m + 1)) ≤ ε * sqrt (morseChainA T m) := by
  have hsmall := (morseTransition_next_ratio_tendsto T hd).eventually
    (eventually_lt_nhds (pow_pos hε 2))
  filter_upwards [eventually_ge_atTop T.index, eventually_ge_atTop (1 : ℕ), hsmall]
    with m hm hm1 hsmall
  have hAm : 0 < morseChainA T m :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T m (hd m hm)).1
  have hAnext : 0 < morseChainA T (m + 1) :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T (m + 1) (hd (m + 1) (hm.trans (Nat.le_succ m)))).1
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
    nlinarith only [hm1', sq_nonneg ((m : ℝ) - 1)]
  have hq1 : 1 ≤ radialQ m := hsq.trans (radial_nat_sq_le_Q m)
  have hq2 : 1 ≤ radialQ m ^ 2 := by
    nlinarith only [hq1, sq_nonneg (radialQ m - 1)]
  have hfactor : 1 ≤ radialQ m ^ 2 * ((m : ℝ) + 1) := by
    have h := mul_nonneg (sq_nonneg (radialQ m)) (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [hq2, h]
  have hratio0 : 0 ≤ morseChainA T (m + 1) / morseChainA T m :=
    div_nonneg hAnext.le hAm.le
  have hratio_le : morseChainA T (m + 1) / morseChainA T m ≤
      radialQ m ^ 2 * (morseChainA T (m + 1) / morseChainA T m) * ((m : ℝ) + 1) := by
    calc
      _ = 1 * (morseChainA T (m + 1) / morseChainA T m) := (one_mul _).symm
      _ ≤ (radialQ m ^ 2 * ((m : ℝ) + 1)) *
          (morseChainA T (m + 1) / morseChainA T m) :=
        mul_le_mul_of_nonneg_right hfactor hratio0
      _ = _ := by ring
  have hA := (div_lt_iff₀ hAm).mp (hratio_le.trans_lt hsmall)
  calc
    sqrt (morseChainA T (m + 1)) ≤ sqrt (ε ^ 2 * morseChainA T m) :=
      sqrt_le_sqrt hA.le
    _ = ε * sqrt (morseChainA T m) := by
      rw [sqrt_mul (sq_nonneg ε), sqrt_sq hε.le]

/-- One threshold, chosen above any prescribed minimum, and one first
index absorb the transition-cell cost into the preceding-cell decay.
The additive constant becomes a fixed prefactor after exponentiation. -/
theorem matched_morse_cross_exponent (T : MorseChainData)
    (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    (Aq B Co c Cmin : ℝ) (hAq : 0 ≤ Aq) (hCo : 0 ≤ Co) (hc : 0 < c) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ Cmin ≤ Cstar ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, T.index ≤ N ∧ ∀ m j : ℕ, N ≤ m →
        radialFrequencyBand T Cstar (m + 1) j →
        Aq * radialQ (m + 1) + ((m + 1 : ℕ) : ℝ) ^ 2 + B +
            Co * ((j : ℝ) * sqrt (morseChainA T (m + 1))) -
            c * ((j : ℝ) * sqrt (morseChainA T m)) ≤
          C - c / 2 * ((j : ℝ) * sqrt (morseChainA T m)) := by
  obtain ⟨R, D, hshift⟩ := radialQ_shift_le 1
  let coeff : ℝ := (Aq + 1) * R
  let Cstar : ℝ := 1 + |Cmin| + |4 * coeff / (c / 2)|
  have hCstar : 0 < Cstar := by dsimp [Cstar]; positivity
  have hCmin : Cmin ≤ Cstar := by
    dsimp [Cstar]
    linarith only [le_abs_self Cmin, abs_nonneg (4 * coeff / (c / 2))]
  have hscale : 4 * coeff / (c / 2) ≤ Cstar := by
    dsimp [Cstar]
    linarith only [le_abs_self (4 * coeff / (c / 2)), abs_nonneg Cmin]
  obtain ⟨C, _, hinner⟩ := inner_suppression_exponent
    (c₁ := coeff) (c₂ := 0) (c₃ := c / 2) (Cstar := Cstar)
    (le_refl 0) (by positivity) hCstar hscale
  have hε : 0 < (c / 4) / (Co + 1) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (matched_morse_adjacent_sqrt_small T hd hε)
  let total : ℝ := C + (Aq + 1) * D + B
  refine ⟨Cstar, hCstar, hCmin, |total|, abs_nonneg _, max T.index N, le_max_left _ _, ?_⟩
  intro m j hm hband
  have hmIndex : T.index ≤ m := (le_max_left T.index N).trans hm
  have hnext := hN m ((le_max_right T.index N).trans hm)
  have ht := morseTransition_earlier_cap_action T hCstar hd hband hmIndex (Nat.lt_succ_self m)
  have ht0 : 0 ≤ (j : ℝ) * sqrt (morseChainA T m) :=
    mul_nonneg (Nat.cast_nonneg j) (sqrt_nonneg _)
  have hdecay := hinner (radialQ m) ((j : ℝ) * sqrt (morseChainA T m))
    (radialQ_nonneg m) ht
  simp only [zero_mul, add_zero] at hdecay
  have hqscaled := mul_le_mul_of_nonneg_left (hshift m) (show 0 ≤ Aq + 1 by linarith)
  have hcost : Aq * radialQ (m + 1) + ((m + 1 : ℕ) : ℝ) ^ 2 + B ≤
      coeff * radialQ m + ((Aq + 1) * D + B) := by
    dsimp only [coeff]
    nlinarith only [hqscaled, radial_nat_sq_le_Q (m + 1)]
  have hεcost : Co * ((c / 4) / (Co + 1)) ≤ c / 4 :=
    mul_div_succ_le hCo (by positivity)
  have hnextScaled := mul_le_mul_of_nonneg_left hnext
    (mul_nonneg hCo (Nat.cast_nonneg (α := ℝ) j))
  have hcore : Co * ((j : ℝ) * sqrt (morseChainA T (m + 1))) ≤
      (c / 4) * ((j : ℝ) * sqrt (morseChainA T m)) := by
    calc
      _ = (Co * (j : ℝ)) * sqrt (morseChainA T (m + 1)) := by ring
      _ ≤ (Co * (j : ℝ)) * (((c / 4) / (Co + 1)) * sqrt (morseChainA T m)) :=
        hnextScaled
      _ = (Co * ((c / 4) / (Co + 1))) * ((j : ℝ) * sqrt (morseChainA T m)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hεcost ht0
  have hconst : C + (Aq + 1) * D + B ≤ |total| := le_abs_self total
  nlinarith only [hcost, hcore, hdecay, hconst]

end ContinuousFlexibility.Radial
