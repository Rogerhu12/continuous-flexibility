module

public import ContinuousFlexibility.Radial.InnerFrequencySuppression

/-!
# The order of choices for the actual inner bands

The threshold is chosen before the starting index. The estimate then
holds for every actual Morse chain starting at that index, so choosing
or truncating the geometric realization afterwards does not change the
argument. The central and cone length thresholds are chosen after the
starting index and may use its already fixed constants.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

/-- The starting index works for every actual Morse realization with that
index, every later cell, and every frequency in every later band. -/
theorem exists_inner_ordered_morse_choices (a : ℝ) {c₁ c₂ c₃ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 < c₃) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ 4 * (c₁ + 5) / c₃ ≤ Cstar ∧
      ∀ η : ℝ, 0 < η → ∀ initial : ℕ, ∃ N : ℕ,
        initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
        ∀ T : MorseChainData, T.index = N →
          (∀ m, N ≤ m → T.d m = morseChainInteger m) →
          ∀ m n j : ℕ, N ≤ m → m < n → radialFrequencyBand T Cstar n j →
            exp (c₁ * radialQ m +
              c₂ * log (1 + (j : ℝ) * sqrt (morseChainA T m)) -
              c₃ * ((j : ℝ) * sqrt (morseChainA T m))) < η ∧
            (j : ℝ) * exp (c₁ * radialQ m +
              c₂ * log (1 + (j : ℝ) * sqrt (morseChainA T m)) -
              c₃ * ((j : ℝ) * sqrt (morseChainA T m))) < η := by
  let Cstar : ℝ := 1 + 4 * (c₁ + 5) / c₃
  have hCstar : 0 < Cstar := by dsimp only [Cstar]; positivity
  have hscale : 4 * (c₁ + 5) / c₃ ≤ Cstar := by dsimp only [Cstar]; linarith
  refine ⟨Cstar, hCstar, hscale, ?_⟩
  intro η hη initial
  obtain ⟨N, hN, hlarge, hweight, hsmall⟩ := inner_uniform_frequency_suppression
    radialQ inner_radialQ_tendsto a initial hc₂ hc₃ hCstar hscale hη
  refine ⟨N, hN, hlarge, hweight, ?_⟩
  intro T hindex hd m n j hm hmn hband
  have hmIndex : T.index ≤ m := by simpa only [hindex] using hm
  have hd' : ∀ k, T.index ≤ k → T.d k = morseChainInteger k := by
    intro k hk
    exact hd k (by simpa only [hindex] using hk)
  have haction := morseTransition_earlier_cap_action T hCstar hd' hband hmIndex hmn
  have hm1 : 1 ≤ m := by omega
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hQpos : 0 < radialQ m := lt_of_lt_of_le
    (by nlinarith only [hmReal] : (0 : ℝ) < (m : ℝ) ^ 2) (radial_nat_sq_le_Q m)
  have hj1 : 1 ≤ j := by
    by_contra h
    have hjzero : j = 0 := by omega
    rw [hjzero, Nat.cast_zero, zero_mul] at haction
    exact (not_le_of_gt (mul_pos hCstar hQpos)) haction
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hlog : log (j : ℝ) ≤
      log (1 + (j : ℝ) * sqrt (morseChainA T m)) + 5 * radialQ m :=
    (log_le_log (zero_lt_one.trans_le hj) (by linarith : (j : ℝ) ≤ 1 + (j : ℝ))).trans
      (inner_morse_frequency_log_bound T (hd m hm) hm1 (Nat.cast_nonneg j))
  exact hsmall m hm _ j haction hj hlog

/-- The central cut and cone length are chosen after all constants that
may depend on N. Both estimates are uniform for every larger cut or length
and every unbounded frequency. -/
theorem exists_inner_ordered_head_choices
    {Acentral Acone bcentral bcone dcentral dcone ccentral ccone η : ℝ}
    (hbcentral : 0 ≤ bcentral) (hbcone : 0 ≤ bcone)
    (hdcentral : 0 ≤ dcentral) (hdcone : 0 ≤ dcone)
    (hccentral : 0 < ccentral) (hccone : 0 < ccone) (hη : 0 < η)
    (centralFloor coneFloor : ℝ) :
    ∃ X₀ L₀ : ℝ, 8 ≤ X₀ ∧ centralFloor ≤ X₀ ∧ 1 ≤ L₀ ∧ coneFloor ≤ L₀ ∧
      (∀ X j : ℝ, X₀ ≤ X → 1 ≤ j →
        exp (Acentral + bcentral * log (1 + j) + dcentral * log (1 + X ^ 2) -
          ccentral * j * X ^ 2) < η ∧
        j * exp (Acentral + bcentral * log (1 + j) + dcentral * log (1 + X ^ 2) -
          ccentral * j * X ^ 2) < η) ∧
      (∀ L j : ℝ, L₀ ≤ L → 1 ≤ j →
        exp (Acone + bcone * log (1 + j) + dcone * log (1 + L) -
          ccone * j * L) < η ∧
        j * exp (Acone + bcone * log (1 + j) + dcone * log (1 + L) -
          ccone * j * L) < η) := by
  obtain ⟨Y, hY, hcentral⟩ := inner_product_frequency_suppression
    (A := Acentral) hbcentral hdcentral hccentral hη
  obtain ⟨L, hL, hcone⟩ := inner_product_frequency_suppression
    (A := Acone) hbcone hdcone hccone hη
  let X₀ := max 8 (max centralFloor Y)
  let L₀ := max coneFloor L
  have hX8 : 8 ≤ X₀ := le_max_left _ _
  have hXfloor : centralFloor ≤ X₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hXY : Y ≤ X₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hL0 : L ≤ L₀ := le_max_right _ _
  refine ⟨X₀, L₀, hX8, hXfloor, hL.trans hL0, le_max_left _ _, ?_, ?_⟩
  · intro X j hX hj
    have hX1 : 1 ≤ X := hY.trans (hXY.trans hX)
    have hYY : Y ≤ X ^ 2 := by nlinarith only [hXY.trans hX, hX1]
    exact hcentral (X ^ 2) hYY j hj
  · intro L' j hL' hj
    exact hcone L' (hL0.trans hL') j hj

end ContinuousFlexibility.Radial
