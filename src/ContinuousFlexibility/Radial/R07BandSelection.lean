module

public import ContinuousFlexibility.Radial.HeightBandCount
public import ContinuousFlexibility.Radial.HeightSimultaneousSelection

/-!
# One height sequence for both endpoints

The public R07 data use the same height ratio sequence at the two endpoints.
The exceptional sets must therefore be summed over both endpoints before
applying the product selection theorem. Halving the one-endpoint tolerance
gives exactly the same total exceptional-set budget.

This file also extracts the canonical Morse integers and the frequency-band
partition directly from a realized chain. The final selection theorem still
has explicit analytic hypotheses about the incoming and natural states;
those hypotheses are supplied by the concrete radial construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Function Real
open scoped ENNReal

/-- An even frequency together with its transition-band index. -/
abbrev R07BandFrequency (T : Statements.MorseChainData) (C : ℝ) :=
  {p : ℕ × ℕ // 2 ≤ p.2 ∧ Even p.2 ∧ Statements.radialFrequencyBand T C p.1 p.2}

/-- Both endpoints impose conditions on the same coordinate of the height cube. -/
abbrev R07MatchingCondition (T : Statements.MorseChainData) (C : ℝ) :=
  Bool × R07BandFrequency T C

/-- The first realization clause fixes the integer of every retained cell. -/
theorem morseChainRealization_integer_eq {T : Statements.MorseChainData}
    {σ C : ℕ → ℝ} {D : Statements.ReferenceData}
    (h : Statements.MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n) :
    T.d n = morseChainInteger n := by
  obtain ⟨hexp, hns, hmin⟩ := h.1 n hn
  apply le_antisymm
  · exact le_of_not_gt fun hlt =>
      (morseChainInteger_spec n).2 (hmin (morseChainInteger n)
        (morseChainInteger_spec n).1 hlt)
  · exact le_of_not_gt fun hlt =>
      hns (morseChainInteger_minimal n (T.d n) hexp hlt)

/-- Every frequency at least two has one transition cell in a realized chain. -/
theorem morseChainRealization_existsUnique_band {T : Statements.MorseChainData}
    {σ K : ℕ → ℝ} {D : Statements.ReferenceData}
    (h : Statements.MorseChainRealization T σ D K) {C : ℝ} (hC : 0 < C)
    {j : ℕ} (hj : 2 ≤ j) :
    ∃! n : ℕ, Statements.radialFrequencyBand T C n j :=
  morseTransition_existsUnique_band T hC
    (fun _ hn => morseChainRealization_integer_eq h hn) hj

private theorem tsum_two_endpoints_half {α : Type*} (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    (∑' k : Bool × α, ENNReal.ofReal (f k.2 / 2)) =
      ∑' a : α, ENNReal.ofReal (f a) := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_fintype, Fintype.sum_bool]
  rw [← ENNReal.ofReal_add (div_nonneg (hf a) (by norm_num))
    (div_nonneg (hf a) (by norm_num))]
  congr 1
  ring

/-- A common positive tolerance pays for both endpoint exceptional sets. -/
theorem exists_r07_height_tolerance (T : Statements.MorseChainData) {C : ℝ}
    (hC : 0 < C) (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 48 ∧
      ∑' k : R07MatchingCondition T C,
        ENNReal.ofReal (192 * (c₀ * exp (-(k.2.1.1 : ℝ) ^ 2))) < 1 := by
  obtain ⟨b, hb, hb48, hsum⟩ := exists_height_tolerance_band_sum_lt T hC hd
  refine ⟨b / 2, half_pos hb, (half_le_self hb.le).trans hb48, ?_⟩
  calc
    _ = ∑' k : R07MatchingCondition T C,
        ENNReal.ofReal ((192 * (b * exp (-(k.2.1.1 : ℝ) ^ 2))) / 2) := by
          apply tsum_congr
          intro k
          congr 1
          ring
    _ = ∑' p : R07BandFrequency T C,
        ENNReal.ofReal (192 * (b * exp (-(p.1.1 : ℝ) ^ 2))) :=
          tsum_two_endpoints_half
            (fun p : R07BandFrequency T C => 192 * (b * exp (-(p.1.1 : ℝ) ^ 2)))
            (fun p : R07BandFrequency T C => by positivity)
    _ < 1 := hsum

/-- The two-endpoint tolerance needs no extra arithmetic assumption for a
realized chain. -/
theorem exists_r07_height_tolerance_of_realization {T : Statements.MorseChainData}
    {σ K : ℕ → ℝ} {D : Statements.ReferenceData}
    (h : Statements.MorseChainRealization T σ D K) {C : ℝ} (hC : 0 < C) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 48 ∧
      ∑' k : R07MatchingCondition T C,
        ENNReal.ofReal (192 * (c₀ * exp (-(k.2.1.1 : ℝ) ^ 2))) < 1 :=
  exists_r07_height_tolerance T hC
    (fun _ hn => morseChainRealization_integer_eq h hn)

/-- With the analytic state estimates established uniformly at both endpoints,
one height sequence separates all matching lines in all frequency bands. -/
theorem exists_r07_heights_all_angles_separated (T : Statements.MorseChainData)
    (C c₀ : ℝ) (η : R07MatchingCondition T C → ℝ)
    (a Ξ : R07MatchingCondition T C → (ℕ → ℝ) → ℝ)
    (Y B : R07MatchingCondition T C → (ℕ → ℝ) → ℝ × ℝ)
    (hc₀ : 0 < c₀) (hc₀48 : c₀ ≤ 1 / 48)
    (hη : ∀ k, 0 ≤ η k ∧ η k ≤ (c₀ * exp (-(k.2.1.1 : ℝ) ^ 2)) / 4)
    (ha : ∀ k, ∀ σ ∈ heightCube, a k σ ∈ Icc (-(3 : ℝ) / 2) (-1 / 2))
    (hΞ : ∀ k, ∀ σ ∈ heightCube, 0 < Ξ k σ)
    (hB : ∀ k, ∀ σ ∈ heightCube, B k σ ≠ (0, 0))
    (hY : ∀ k, ∀ σ ∈ heightCube,
      |(Y k σ).1 - 1| ≤ η k ∧ |(Y k σ).2 - a k σ| ≤ η k)
    (ha_indep : ∀ k, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      a k (update σ k.2.1.1 t) = a k σ)
    (hΞ_indep : ∀ k, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      Ξ k (update σ k.2.1.1 t) = Ξ k σ)
    (hB_indep : ∀ k, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      B k (update σ k.2.1.1 t) = B k σ)
    (hYcont : ∀ k, ContinuousOn (Y k) heightCube)
    (hΞcont : ∀ k, ContinuousOn (Ξ k) heightCube)
    (hBcont : ∀ k, ContinuousOn (B k) heightCube)
    (hsum : ∑' k : R07MatchingCondition T C,
      ENNReal.ofReal (192 * (c₀ * exp (-(k.2.1.1 : ℝ) ^ 2))) < 1) :
    ∃ σ : ℕ → ℝ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) ∧
      ∀ k : R07MatchingCondition T C,
        c₀ * exp (-(k.2.1.1 : ℝ) ^ 2) ≤
          Statements.radialAngleSine (Y k σ)
            (morseHeightOuterState (Ξ k σ) (σ k.2.1.1) (B k σ)) := by
  have hδ : ∀ k : R07MatchingCondition T C,
      0 < c₀ * exp (-(k.2.1.1 : ℝ) ^ 2) ∧
        c₀ * exp (-(k.2.1.1 : ℝ) ^ 2) ≤ 1 / 48 := by
    intro k
    refine ⟨mul_pos hc₀ (exp_pos _), ?_⟩
    have he : exp (-(k.2.1.1 : ℝ) ^ 2) ≤ 1 :=
      exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
    calc
      _ ≤ c₀ * 1 := mul_le_mul_of_nonneg_left he hc₀.le
      _ = c₀ := mul_one _
      _ ≤ 1 / 48 := hc₀48
  obtain ⟨σ, hσ, hangle⟩ := exists_heights_all_angles_separated
    (fun k : R07MatchingCondition T C => k.2.1.1)
    (fun k => c₀ * exp (-(k.2.1.1 : ℝ) ^ 2)) η a Ξ Y B
    hδ hη ha hΞ hB hY ha_indep hΞ_indep hB_indep hYcont hΞcont hBcont hsum
  exact ⟨σ, mem_heightCube.mp hσ, hangle⟩

end ContinuousFlexibility.Radial
