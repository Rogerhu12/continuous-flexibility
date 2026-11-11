import ContinuousFlexibility.Radial.R07UniformSelection

/-!
# Selecting only the noninitial bands

The initial band is finite and is handled by the middle-cone choice.
All later conditions form a subtype of the full two-endpoint condition
set, so the same previously chosen height tolerance pays for them.
No artificial matching states are needed at the initial band.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ENNReal

abbrev R07LaterCondition (T : Statements.MorseChainData) (C : ℝ) :=
  {k : R07MatchingCondition T C // T.index < k.2.1.1}

abbrev R07FirstFrequency (T : Statements.MorseChainData) (C : ℝ) :=
  {j : ℕ // 2 ≤ j ∧ Even j ∧ Statements.radialFrequencyBand T C T.index j}

theorem r07_first_band_finite (T : Statements.MorseChainData) (C : ℝ) :
    Set.Finite {j : ℕ | 2 ≤ j ∧ Even j ∧ Statements.radialFrequencyBand T C T.index j} := by
  apply (Finset.finite_toSet (Finset.range ⌈Statements.radialFrequencyThreshold T C T.index⌉₊)).subset
  intro j hj
  exact Finset.mem_range.mpr (Nat.lt_ceil.mpr hj.2.2.2.2)

noncomputable instance (T : Statements.MorseChainData) (C : ℝ) :
    Fintype (R07FirstFrequency T C) := (r07_first_band_finite T C).fintype

theorem r07_later_budget_le (T : Statements.MorseChainData) (C c₀ : ℝ) :
    (∑' k : R07LaterCondition T C,
      ENNReal.ofReal (192 * (c₀ * exp (-(k.1.2.1.1 : ℝ) ^ 2)))) ≤
    ∑' k : R07MatchingCondition T C,
      ENNReal.ofReal (192 * (c₀ * exp (-(k.2.1.1 : ℝ) ^ 2))) :=
  ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
    (fun k : R07MatchingCondition T C =>
      ENNReal.ofReal (192 * (c₀ * exp (-(k.2.1.1 : ℝ) ^ 2))))

/-- A single sequence separates every noninitial matching condition.
The tolerance is the same one fixed before the chain was constructed. -/
theorem exists_r07_later_heights (T : Statements.MorseChainData) (C c₀ : ℝ)
    (a Ξ : R07LaterCondition T C → (ℕ → ℝ) → ℝ)
    (Y B : R07LaterCondition T C → (ℕ → ℝ) → ℝ × ℝ)
    (hc₀ : 0 < c₀) (hc₀48 : c₀ ≤ 1 / 48)
    (ha : ∀ k, ∀ σ ∈ heightCube, a k σ ∈ Icc (-(3 : ℝ) / 2) (-1 / 2))
    (hΞ : ∀ k, ∀ σ ∈ heightCube, 0 < Ξ k σ)
    (hB : ∀ k, ∀ σ ∈ heightCube, B k σ ≠ (0, 0))
    (hY : ∀ k, ∀ σ ∈ heightCube,
      |(Y k σ).1 - 1| ≤ (c₀ * exp (-(k.1.2.1.1 : ℝ) ^ 2)) / 4 ∧
      |(Y k σ).2 - a k σ| ≤ (c₀ * exp (-(k.1.2.1.1 : ℝ) ^ 2)) / 4)
    (ha_indep : ∀ k, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      a k (Function.update σ k.1.2.1.1 t) = a k σ)
    (hΞ_indep : ∀ k, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      Ξ k (Function.update σ k.1.2.1.1 t) = Ξ k σ)
    (hB_indep : ∀ k, ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
      B k (Function.update σ k.1.2.1.1 t) = B k σ)
    (hYcont : ∀ k, ContinuousOn (Y k) heightCube)
    (hΞcont : ∀ k, ContinuousOn (Ξ k) heightCube)
    (hBcont : ∀ k, ContinuousOn (B k) heightCube)
    (hsum : ∑' k : R07MatchingCondition T C,
      ENNReal.ofReal (192 * (c₀ * exp (-(k.2.1.1 : ℝ) ^ 2))) < 1) :
    ∃ σ : ℕ → ℝ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) ∧
      ∀ k : R07LaterCondition T C,
        c₀ * exp (-(k.1.2.1.1 : ℝ) ^ 2) ≤
          Statements.radialAngleSine (Y k σ)
            (morseHeightOuterState (Ξ k σ) (σ k.1.2.1.1) (B k σ)) := by
  have hδ : ∀ k : R07LaterCondition T C,
      0 < c₀ * exp (-(k.1.2.1.1 : ℝ) ^ 2) ∧
        c₀ * exp (-(k.1.2.1.1 : ℝ) ^ 2) ≤ 1 / 48 := by
    intro k
    refine ⟨mul_pos hc₀ (exp_pos _), ?_⟩
    calc
      _ ≤ c₀ * 1 := mul_le_mul_of_nonneg_left
        (exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))) hc₀.le
      _ = c₀ := mul_one _
      _ ≤ _ := hc₀48
  have hsum' := (r07_later_budget_le T C c₀).trans_lt hsum
  obtain ⟨σ, hσ, hangle⟩ := exists_heights_all_angles_separated
    (fun k : R07LaterCondition T C => k.1.2.1.1)
    (fun k => c₀ * exp (-(k.1.2.1.1 : ℝ) ^ 2))
    (fun k => (c₀ * exp (-(k.1.2.1.1 : ℝ) ^ 2)) / 4) a Ξ Y B hδ
    (fun k => ⟨by positivity, le_rfl⟩) ha hΞ hB hY ha_indep hΞ_indep hB_indep
    hYcont hΞcont hBcont hsum'
  exact ⟨σ, mem_heightCube.mp hσ, hangle⟩

end ContinuousFlexibility.Radial
