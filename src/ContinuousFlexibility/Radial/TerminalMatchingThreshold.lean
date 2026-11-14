module

public import ContinuousFlexibility.Radial.TerminalMatchingSuppression

/-!
# Matching suppression with an external frequency threshold

The threshold may be fixed above any external constant before selecting
the margin, propagation constant, or first index. The frequency band
keeps its original definition throughout.

The lower band edge controls every earlier cap, in particular cap m for
band m+1. The action of the transition cell m+1 has an upper band bound,
so no lower cap-action estimate is asserted for that cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real
open scoped Topology

/-- An external floor for the threshold becomes an action floor on an
earlier positive-index cap, and only on such an earlier cap. -/
theorem terminalMatching_band_earlier_action_ge (T : Statements.MorseChainData)
    {Cstar Cmin : ℝ} (hCstar : 0 < Cstar) (hmin : Cmin ≤ Cstar)
    (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    {n m j : ℕ} (hband : Statements.radialFrequencyBand T Cstar n j)
    (hmIndex : T.index ≤ m) (hm1 : 1 ≤ m) (hmn : m < n) :
    Cmin ≤ terminalMatchingAction T m j := by
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hQ : 1 ≤ Statements.radialQ m := by
    have hs : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hm₁ 2
    exact hs.trans (radial_nat_sq_le_Q m)
  exact (hmin.trans (le_mul_of_one_le_right hCstar.le hQ)).trans
    (morseTransition_earlier_cap_action T hCstar hd hband hmIndex hmn)

/-- In contrast, the upper band edge is an upper bound on the action of
the transition cell itself. This records the index distinction. -/
theorem terminalMatching_band_transition_action_lt (T : Statements.MorseChainData)
    {Cstar : ℝ} (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    {n j : ℕ} (hband : Statements.radialFrequencyBand T Cstar n j) :
    terminalMatchingAction T n j < Cstar * Statements.radialQ n := by
  have hA : 0 < Statements.morseChainA T n :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T n (hd n hband.1)).1
  have hupper := hband.2.2
  change (j : ℝ) < Cstar * Statements.radialQ n / sqrt (Statements.morseChainA T n) at hupper
  exact (lt_div_iff₀ (sqrt_pos.mpr hA)).mp hupper

/-- The same four-quarter budget works for every larger threshold.
Neither its band nor the actual adjacent actions are changed. -/
theorem terminalMatching_band_suppression_of_threshold (T : Statements.MorseChainData)
    (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    {C c Cstar : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hCstar : 0 < Cstar)
    (hscale : 64 * C + 16 ≤ c * Cstar) (Co : ℝ) (hCo : 0 ≤ Co)
    (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ N : ℕ, T.index ≤ N ∧ 1 ≤ N ∧ ∀ m : ℕ, N ≤ m → ∀ j : ℕ,
      Statements.radialFrequencyBand T Cstar (m + 1) j →
      (Statements.radialE (m + 1) ^ C * (terminalMatchingMargin c₀ (m + 1))⁻¹ *
        exp (Co * terminalMatchingAction T (m + 1) j -
          c * terminalMatchingAction T m j) < 1 / 16) ∧
      ∀ r s : ℝ, terminalMatchingAction T m j ≤ r → terminalMatchingAction T m j ≤ s →
        Statements.radialE (m + 1) ^ C * exp (-c * r - c * s) <
          terminalMatchingMargin c₀ (m + 1) / 16 := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (|log c₀| + log 16 + 1)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (terminalMatching_adjacent_action_small T hd hc hCo)
  refine ⟨max T.index (max 1 (max N₀ N₁)), by omega, by omega, ?_⟩
  intro m hm j hband
  have hmIndex : T.index ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hx : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hq₀ := radialQ_nonneg m
  have hraw := mul_le_mul_of_nonneg_left
    (morseTransition_earlier_cap_action T hCstar hd hband hmIndex (Nat.lt_succ_self m)) hc.le
  have ht : (64 * C + 16) * Statements.radialQ m ≤
      c * ((j : ℝ) * sqrt (Statements.morseChainA T m)) := by
    calc
      _ ≤ (c * Cstar) * Statements.radialQ m := mul_le_mul_of_nonneg_right hscale hq₀
      _ ≤ _ := by simpa only [mul_assoc] using hraw
  have hcoeff := mul_le_mul_of_nonneg_left (terminalMatching_radialQ_succ_le hm1) hC
  have hCQ := mul_nonneg hC hq₀
  have hsq : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * Statements.radialQ m := by
    have h := mul_nonneg (sub_nonneg.mpr hx) (by positivity : 0 ≤ 3 * (m : ℝ) + 1)
    push_cast
    nlinarith only [h, radial_nat_sq_le_Q m]
  have hlog : |log c₀| + log 16 + 1 ≤ Statements.radialQ m := by
    have hcast := hN₀.trans (Nat.cast_le.mpr (by omega : N₀ ≤ m))
    have h := mul_nonneg (sub_nonneg.mpr hx) (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [hcast, h, radial_nat_sq_le_Q m]
  have hsmall : Statements.radialE (m + 1) ^ C * (terminalMatchingMargin c₀ (m + 1))⁻¹ *
      exp (Co * terminalMatchingAction T (m + 1) j - c * terminalMatchingAction T m j) <
        1 / 16 := by
    apply terminalMatching_small_of_quarter_budgets (m + 1) hc₀
    · dsimp only [terminalMatchingAction]
      nlinarith only [hcoeff, ht, hq₀]
    · dsimp only [terminalMatchingAction]
      nlinarith only [hsq, ht, hCQ]
    · dsimp only [terminalMatchingAction]
      nlinarith only [hlog, ht, hCQ, hq₀]
    · exact hN₁ m (by omega) j
  refine ⟨hsmall, ?_⟩
  intro r s hr hs
  exact terminalMatching_two_attenuations (m + 1) hc₀ hc.le hCo
    (terminalMatchingAction_nonneg T m j) (terminalMatchingAction_nonneg T (m + 1) j)
    hr hs hsmall

/-- Choose one threshold above both 1000 and an external requirement.
All later bands use this same threshold. The floor applies to the actual
preceding cap m of band m+1, as needed for long-cap attenuation. -/
theorem exists_terminalMatching_band_suppression_above (T : Statements.MorseChainData)
    (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    (Cmin : ℝ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ Cstar : ℝ, max 1000 Cmin ≤ Cstar ∧
      ∀ Co : ℝ, 0 ≤ Co → ∀ c₀ : ℝ, 0 < c₀ →
      ∃ N : ℕ, T.index ≤ N ∧ 1 ≤ N ∧ ∀ m : ℕ, N ≤ m → ∀ j : ℕ,
        Statements.radialFrequencyBand T Cstar (m + 1) j →
        max 1000 Cmin ≤ terminalMatchingAction T m j ∧
        (Statements.radialE (m + 1) ^ C * (terminalMatchingMargin c₀ (m + 1))⁻¹ *
          exp (Co * terminalMatchingAction T (m + 1) j -
            c * terminalMatchingAction T m j) < 1 / 16) ∧
        ∀ r s : ℝ, terminalMatchingAction T m j ≤ r → terminalMatchingAction T m j ≤ s →
          Statements.radialE (m + 1) ^ C * exp (-c * r - c * s) <
            terminalMatchingMargin c₀ (m + 1) / 16 := by
  let Cstar : ℝ := max (max 1000 Cmin) ((64 * C + 16) / c)
  have hfloor : max 1000 Cmin ≤ Cstar := le_max_left _ _
  have hCstar : 0 < Cstar :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1000) ((le_max_left _ _).trans hfloor)
  have hscale : 64 * C + 16 ≤ c * Cstar := by
    have hbase : (64 * C + 16) / c ≤ Cstar := le_max_right _ _
    have h := (div_le_iff₀ hc).mp hbase
    nlinarith only [h]
  refine ⟨Cstar, hfloor, ?_⟩
  intro Co hCo c₀ hc₀
  obtain ⟨N, hNI, hN1, hN⟩ :=
    terminalMatching_band_suppression_of_threshold T hd hC hc hCstar hscale Co hCo c₀ hc₀
  refine ⟨N, hNI, hN1, ?_⟩
  intro m hm j hband
  have hcap := terminalMatching_band_earlier_action_ge T hCstar hfloor hd hband
    (hNI.trans hm) (hN1.trans hm) (Nat.lt_succ_self m)
  exact ⟨hcap, hN m hm j hband⟩

end ContinuousFlexibility.Radial
