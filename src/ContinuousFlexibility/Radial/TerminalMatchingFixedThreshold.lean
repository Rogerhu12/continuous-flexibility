module

public import ContinuousFlexibility.Radial.TerminalMatchingStart

/-!
# Terminal suppression after a common frequency threshold is fixed

The Morse compression may choose any threshold above the explicit
terminal floor. Only the initial index is chosen afterwards. This
keeps the threshold shared by the local models and the selected tail.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

theorem terminalMatching_uniform_start_of_threshold {C c Cstar Cmin c₀ : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hCstar : 0 < Cstar)
    (hscale : 64 * C + 16 ≤ c * Cstar) (hfloor : Cmin ≤ Cstar) (hc₀ : 0 < c₀) :
    ∃ N : ℕ, 100 ≤ N ∧
      ∀ T : MorseChainData, (∀ m, T.d m = morseChainInteger m) → N ≤ T.index →
      ∀ m : ℕ, T.index ≤ m → ∀ j : ℕ, radialFrequencyBand T Cstar (m + 1) j →
        Cmin ≤ terminalMatchingAction T m j ∧
        ∀ r s : ℝ, terminalMatchingAction T m j ≤ r → terminalMatchingAction T m j ≤ s →
          radialE (m + 1) ^ C * exp (-c * r - c * s) <
            terminalMatchingMargin c₀ (m + 1) / 16 := by
  obtain ⟨S, _, ⟨G⟩⟩ := exists_morseChainGeometry 0
  obtain ⟨N₀, hNS, _, hN⟩ := terminalMatching_band_suppression_of_threshold S
    (fun m _ => G.d_exact m) hC hc hCstar hscale 0 (by norm_num) c₀ hc₀
  refine ⟨max 100 N₀, le_max_left _ _, ?_⟩
  intro T hT hNT m hm j hband
  have hN₀m : N₀ ≤ m := ((le_max_right _ _).trans hNT).trans hm
  have hSm : S.index ≤ m := hNS.trans hN₀m
  have hm₁ : 1 ≤ m := by have := (le_max_left 100 N₀).trans (hNT.trans hm); omega
  have hbandS := canonicalMorseChain_later_band G.d_exact hT hSm hm hband
  have hresult := (hN m hN₀m j hbandS).2
  refine ⟨terminalMatching_band_earlier_action_ge T hCstar hfloor
    (fun k _ => hT k) hband hm hm₁ (Nat.lt_succ_self m), ?_⟩
  simpa only [canonicalMorseChain_action_eq G.d_exact hT] using hresult

/-- A single additional coefficient power pays for the sum of the
actual energy error and the inverse times the squared source cost. -/
theorem terminalMatching_coefficient_power {E e p g : ℝ}
    (hE : 2 ≤ E) :
    E ^ e + E ^ g * (E ^ p) ^ (2 : ℕ) ≤ E ^ (1 + max e (g + 2 * p)) := by
  have hE₀ : 0 < E := (by norm_num : (0 : ℝ) < 2).trans_le hE
  have hE₁ : 1 ≤ E := (by norm_num : (1 : ℝ) ≤ 2).trans hE
  have he : E ^ e ≤ E ^ max e (g + 2 * p) :=
    rpow_le_rpow_of_exponent_le hE₁ (le_max_left _ _)
  have hp : E ^ g * (E ^ p) ^ (2 : ℕ) = E ^ (g + 2 * p) := by
    rw [pow_two, ← rpow_add hE₀, ← rpow_add hE₀]
    congr 1
    ring
  rw [hp]
  have hg : E ^ (g + 2 * p) ≤ E ^ max e (g + 2 * p) :=
    rpow_le_rpow_of_exponent_le hE₁ (le_max_right _ _)
  calc
    _ ≤ 2 * E ^ max e (g + 2 * p) := by linarith only [he, hg]
    _ ≤ E * E ^ max e (g + 2 * p) :=
      mul_le_mul_of_nonneg_right hE (rpow_nonneg hE₀.le _)
    _ = _ := by rw [rpow_add hE₀, rpow_one]

end ContinuousFlexibility.Radial
