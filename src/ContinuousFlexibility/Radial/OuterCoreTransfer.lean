module

public import ContinuousFlexibility.Radial.OuterJoinFrequency

/-!
# Uniform transfer bounds for the actual ordinary transition core

The preceding physical connector and all three retained-cell pieces
are assembled before estimating the actual state.  The quadratic
constant is independent of the cell index, frequency, and heights.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

def outerCoreQuadraticExponent (C : ℕ → ℝ) (K a Cstar L : ℝ) : ℝ :=
  4 * L + 10 * outerFrequencyExponent Cstar + 500000 +
    (4 * (outerJoinPrefactor C K a + (outerFrequencyExponent Cstar + L + 32)) + 2)

def outerCoreActionExponent (C : ℕ → ℝ) (K a : ℝ) : ℝ :=
  10 + 2 * sqrt (outerJoinActionCoefficient C K a)

theorem morseOuterCore_factor_le_frequency_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale : ℝ} {n j : ℕ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (side : Bool) (hn : T.index < n) (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2)) :
    morseOuterCoreEnergyFactor T D side n (j : ℝ) scale (exp (L * (n : ℝ) ^ 2)) ≤
      exp (outerCoreQuadraticExponent C K D.a Cstar L * (n : ℝ) ^ 2 +
        outerCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) := by
  have hcellBound := morse_cell_factor_le_frequency_exp (by omega : 1 ≤ n) (h.d_eq n hn.le) hband
  have hjoinBound := morse_preceding_join_factor_le_frequency_exp h hσ hcell hscale hL side hn hband hhi hlo
  unfold morseOuterCoreEnergyFactor
  calc
    _ ≤ ((exp (L * (n : ℝ) ^ 2)) ^ 4 *
        exp ((10 * outerFrequencyExponent Cstar + 500000) * (n : ℝ) ^ 2 +
          10 * ((j : ℝ) * sqrt (morseChainA T n)))) *
        exp ((4 * (outerJoinPrefactor C K D.a + (outerFrequencyExponent Cstar + L + 32)) + 2) *
          (n : ℝ) ^ 2 + 2 * sqrt (outerJoinActionCoefficient C K D.a) *
            ((j : ℝ) * sqrt (morseChainA T n))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcellBound (by positivity))
        hjoinBound (outerPositivePhysicalFactor_nonneg _ _ _ _ _) (by positivity)
    _ = _ := by
      rw [outer_exp_pow_four, ← exp_add, ← exp_add]
      congr 1
      dsimp only [outerCoreQuadraticExponent, outerCoreActionExponent]
      ring

/-- Every actual homogeneous state satisfies the same two-direction
core estimate.  No transfer bound is assumed in the hypotheses. -/
theorem morseOuterCore_endpoint_energy_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (side : Bool) (hn : T.index < n) (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2))
    (hstate : ∀ r ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z ((j : ℝ) ^ 2 * deriv D.w r / (scale * r) * u r) r) :
    let l := morseOuterCoreLeft T side n
    let r := morseOuterCoreRight T side n
    let E := exp (outerCoreQuadraticExponent C K D.a Cstar L * (n : ℝ) ^ 2 +
      outerCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n)))
    (u r ^ 2 + z r ^ 2 ≤ (u l ^ 2 + z l ^ 2) * E) ∧
      (u l ^ 2 + z l ^ 2 ≤ (u r ^ 2 + z r ^ 2) * E) := by
  have hM : 1 ≤ exp (L * (n : ℝ) ^ 2) :=
    one_le_exp_iff.mpr (mul_nonneg hL (sq_nonneg _))
  have henergy := morseOuterCore_endpoint_energy h hσ hscale hM side n hn hhi hlo hstate
  have hfactor := morseOuterCore_factor_le_frequency_exp h hσ hcell hscale hL side hn hband hhi hlo
  exact ⟨henergy.1.trans (mul_le_mul_of_nonneg_left hfactor (by positivity)),
    henergy.2.trans (mul_le_mul_of_nonneg_left hfactor (by positivity))⟩

end ContinuousFlexibility.Radial
