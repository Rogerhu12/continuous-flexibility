module

public import ContinuousFlexibility.Radial.TerminalMatchingThreshold
public import ContinuousFlexibility.Radial.MorseChainGeometry

/-!
# A matching start chosen before the actual selected geometry

All canonical chains use the same integer sequence. Their frequency
thresholds and actions therefore agree above their starting indices.
The scalar suppression theorem consequently chooses a single start
before the final chain, selected sequence, and retained heads exist.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

theorem canonicalMorseChain_action_eq {S T : MorseChainData}
    (hS : ∀ m, S.d m = morseChainInteger m)
    (hT : ∀ m, T.d m = morseChainInteger m) (m j : ℕ) :
    terminalMatchingAction S m j = terminalMatchingAction T m j := by
  simp only [terminalMatchingAction, morseChainA, hS, hT]

theorem canonicalMorseChain_later_band {S T : MorseChainData}
    (hS : ∀ m, S.d m = morseChainInteger m)
    (hT : ∀ m, T.d m = morseChainInteger m) {C : ℝ} {m j : ℕ}
    (hmS : S.index ≤ m) (hmT : T.index ≤ m)
    (hband : radialFrequencyBand T C (m + 1) j) :
    radialFrequencyBand S C (m + 1) j := by
  have hthreshold (n : ℕ) : radialFrequencyThreshold S C n = radialFrequencyThreshold T C n := by
    simp only [radialFrequencyThreshold, morseChainA, hS, hT]
  have hlow := hband.2.1
  rw [if_neg (by omega : m + 1 ≠ T.index)] at hlow
  refine ⟨by omega, ?_, ?_⟩
  · rw [if_neg (by omega : m + 1 ≠ S.index), hthreshold]
    exact hlow
  · rw [hthreshold]
    exact hband.2.2

/-- The threshold is fixed first, the later margin and propagation cost
second, and the starting index third. Every subsequently constructed
canonical chain beginning beyond that index satisfies the same budget. -/
theorem exists_terminalMatching_uniform_start (Cmin : ℝ) {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ Cstar : ℝ, max 1000 Cmin ≤ Cstar ∧
      ∀ Co : ℝ, 0 ≤ Co → ∀ c₀ : ℝ, 0 < c₀ →
      ∃ N : ℕ, 100 ≤ N ∧
        ∀ T : MorseChainData, (∀ m, T.d m = morseChainInteger m) → N ≤ T.index →
        ∀ m : ℕ, T.index ≤ m → ∀ j : ℕ, radialFrequencyBand T Cstar (m + 1) j →
          max 1000 Cmin ≤ terminalMatchingAction T m j ∧
          (radialE (m + 1) ^ C * (terminalMatchingMargin c₀ (m + 1))⁻¹ *
            exp (Co * terminalMatchingAction T (m + 1) j -
              c * terminalMatchingAction T m j) < 1 / 16) ∧
          ∀ r s : ℝ, terminalMatchingAction T m j ≤ r → terminalMatchingAction T m j ≤ s →
            radialE (m + 1) ^ C * exp (-c * r - c * s) <
              terminalMatchingMargin c₀ (m + 1) / 16 := by
  obtain ⟨S, _, ⟨G⟩⟩ := exists_morseChainGeometry 0
  obtain ⟨Cstar, hCstar, hchoose⟩ := exists_terminalMatching_band_suppression_above S
    (fun m _ => G.d_exact m) Cmin hC hc
  refine ⟨Cstar, hCstar, ?_⟩
  intro Co hCo c₀ hc₀
  obtain ⟨N₀, hNS, _, hN⟩ := hchoose Co hCo c₀ hc₀
  refine ⟨max 100 N₀, le_max_left _ _, ?_⟩
  intro T hT hNT m hm j hband
  have hN₀m : N₀ ≤ m := ((le_max_right _ _).trans hNT).trans hm
  have hSm : S.index ≤ m := hNS.trans hN₀m
  have hbandS := canonicalMorseChain_later_band G.d_exact hT hSm hm hband
  have hresult := hN m hN₀m j hbandS
  simpa only [canonicalMorseChain_action_eq G.d_exact hT] using hresult

end ContinuousFlexibility.Radial
