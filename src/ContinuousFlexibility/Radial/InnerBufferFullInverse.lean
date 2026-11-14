module

public import ContinuousFlexibility.Statements.RadialTargets
public import ContinuousFlexibility.Radial.MorseFullStatement
public import ContinuousFlexibility.Radial.CentralStatementBridges
public import ContinuousFlexibility.Radial.MorseRealizationBasic
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual full-model inverses for the buffer construction

The unbordered models have one scalar coordinate constrained to zero.
Extending their actual weak Schrödinger inverse by that zero coordinate
does not change the operator bound. This supplies the full-line inverse
clause of the compression hypotheses from the proved Morse and central
spectral theorems, before any cap, action, or error estimate is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped InnerProductSpace

def innerUnborderedFullInverse (G : RadialL2 →L[ℝ] RadialL2) :
    (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ) :=
  (G ∘L ContinuousLinearMap.fst ℝ RadialL2 ℝ).prod 0

theorem innerUnborderedFullInverse_apply (G : RadialL2 →L[ℝ] RadialL2)
    (F : RadialL2 × ℝ) :
    innerUnborderedFullInverse G F = (G F.1, 0) := by
  simp only [innerUnborderedFullInverse, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', zero_apply]

theorem norm_innerUnborderedFullInverse_le (G : RadialL2 →L[ℝ] RadialL2) :
    ‖innerUnborderedFullInverse G‖ ≤ ‖G‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  rw [innerUnborderedFullInverse_apply, Prod.norm_mk, norm_zero,
    max_eq_left (norm_nonneg _)]
  exact (G.le_opNorm F.1).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le F) (norm_nonneg _))

/-- The frozen unbordered graph requires the scalar equation to be zero;
the constructed extension enforces it for every admissible source. -/
theorem exists_innerUnborderedFullInverse {V : ℝ → ℝ} {C : ℝ}
    (h : WeakResolventBound V 0 C) :
    ∃ H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ), ‖H‖ ≤ C ∧
      (∀ F, (false = false → F.2 = 0) →
        BorderedFullGraph V 0 false (H F) F) ∧
      (∀ U F, BorderedFullGraph V 0 false U F → H F = U) := by
  obtain ⟨G, hnorm, hgraph, hunique⟩ := h
  refine ⟨innerUnborderedFullInverse G,
    (norm_innerUnborderedFullInverse_le G).trans hnorm, ?_, ?_⟩
  · intro F hF
    rw [innerUnborderedFullInverse_apply]
    refine ⟨?_, rfl, hF rfl⟩
    simpa only [zero_smul, add_zero] using hgraph F.1
  · intro U F hUF
    have hUF' : WeakSchrodingerGraph V U.1 F.1 ∧ U.2 = 0 ∧ F.2 = 0 := hUF
    rw [innerUnborderedFullInverse_apply]
    apply Prod.ext
    · apply hunique U.1 F.1
      simpa only [zero_smul, add_zero] using hUF'.1
    · exact hUF'.2.1.symm

/-- The same actual nonsquare Morse parameter supplies the full-line
inverse for every frequency j≥2, with the explicit coefficient cost. -/
theorem exists_innerMorseFullInverse (d j : ℕ) (hd : 1 < d)
    (hns : ¬ ∃ k : ℕ, k ^ 2 = d) (hj : 2 ≤ j) :
    let A := ((d : ℝ) ^ (-1 / 2 : ℝ) + 2 * (d : ℝ) ^ (-9 / 2 : ℝ)) ^ 2
    let B := (d : ℝ) ^ (-9 : ℝ)
    ActualClosedFormRealization (morsePotential j A B) ∧
      ∃ H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ),
        ‖H‖ ≤ 8 * (d : ℝ) ^ 9 ∧
        (∀ F, (false = false → F.2 = 0) →
          BorderedFullGraph (morsePotential j A B) 0 false (H F) F) ∧
        (∀ U F, BorderedFullGraph (morsePotential j A B) 0 false U F → H F = U) := by
  have hmodel := (morse_R04_statement d hd hns).2.2.1 j hj
  exact ⟨hmodel.1.1, exists_innerUnborderedFullInverse hmodel.2⟩

/-- This specialization uses the actual integer of an arbitrary realized
chain; neither a later tail selection nor an inverse postulate is needed. -/
theorem exists_innerMorseChainFullInverse {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (n j : ℕ) (hn : T.index ≤ n) (hj : 2 ≤ j) :
    ActualClosedFormRealization (morsePotential j (morseChainA T n) (morseChainB T n)) ∧
      ∃ H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ),
        ‖H‖ ≤ 8 * (T.d n : ℝ) ^ 9 ∧
        (∀ F, (false = false → F.2 = 0) →
          BorderedFullGraph (morsePotential j (morseChainA T n) (morseChainB T n))
            0 false (H F) F) ∧
        (∀ U F, BorderedFullGraph
          (morsePotential j (morseChainA T n) (morseChainB T n)) 0 false U F → H F = U) := by
  have hd : 1 < T.d n := by
    rw [h.d_eq n hn]
    exact (show 1 < 2 by decide).trans_le (morseChainInteger_ge_two n)
  exact exists_innerMorseFullInverse (T.d n) j hd (h.1 n hn).2.1 hj

/-- Away from the central ground frequency the actual central spectral
inverse supplies the corresponding unbordered full-line block. -/
theorem exists_innerCentralFullInverse (n : ℕ) (hn : 2 ≤ n) :
    ∃ H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ),
      ‖H‖ ≤ 2 / centralGapDelta ∧
      (∀ F, (false = false → F.2 = 0) →
        BorderedFullGraph (centralPotential (2 * n)) 0 false (H F) F) ∧
      (∀ U F, BorderedFullGraph (centralPotential (2 * n)) 0 false U F → H F = U) :=
  exists_innerUnborderedFullInverse (centralWeakResolventBound_statement n hn)

end ContinuousFlexibility.Radial
