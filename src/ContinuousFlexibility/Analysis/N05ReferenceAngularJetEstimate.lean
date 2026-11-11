import ContinuousFlexibility.Analysis.N05ReferenceAngularJetParseval
import ContinuousFlexibility.Analysis.N05ReferenceAngularWeighted
import ContinuousFlexibility.Radial.R11bWeightedCellClosure

/-!
# The same inverse bounds actual finite angular derivatives

The finite high projections have ordinary angular derivatives of every
order. Their frozen weighted energies equal the frequency-weighted
singleton energies exactly. The common reference inverse therefore obeys
one estimate for all these derivative orders, with no extra material loss.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem n05_referenceHighAngularJet_source_norm {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) (J : Finset ℕ) (b : ℕ) :
    SourceDerivativeMember D γ M (n05_referenceHighAngularJet J b F.1) ∧
      sourceNormSquare D γ M (n05_referenceHighAngularJet J b F.1, 0) =
        ∑ n ∈ J, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          n05_referenceHighSourceSquare D γ M F n := by
  have hs (n : ℕ) (_hn : n ∈ J) :
      Summable (sourceCellSquare D γ M (referenceBasisProjection {n + 2} F.1)) := by
    apply (n05_referenceHighProjection_sourceMember hD hF
      (I := {n + 2}) ?_).2.1
    intro k hk
    simp only [Finset.mem_singleton] at hk
    omega
  obtain ⟨hc, hsum, heq⟩ := n05_referenceHighAngularJet_weighted_sum
    hD.choose_spec.1.2.1.le hF.1 J b
    (fun m => Real.exp (2 * M * radialQ (D.cellIndex m) +
      2 * γ * radialS (D.cellIndex m))) hs
  refine ⟨⟨hc, hsum⟩, ?_⟩
  simpa only [sourceNormSquare, sourceCellSquare, n05_referenceHighSourceSquare,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using heq

theorem n05_referenceHighAngularJet_output_norm {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M a : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputRealization D γ M a U) (J : Finset ℕ) (b : ℕ) :
    RadialCellIntegrable D (n05_referenceHighAngularJet J b U.1) ∧
      Summable (outputCellSquare D γ M (n05_referenceHighAngularJet J b U.1)) ∧
      outputNormSquare D γ M 0 (n05_referenceHighAngularJet J b U.1, 0) =
        ∑ n ∈ J, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          n05_referenceHighOutputSquare D γ M U n := by
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hcell := r11b_cellIntegrable_of_global_memLp hpart
    (r11b_output_memLp hD hborder hγ ⟨a, hU⟩)
  have hs (n : ℕ) (_hn : n ∈ J) :
      Summable (outputCellSquare D γ M (referenceBasisProjection {n + 2} U.1)) := by
    have hI : ∀ k ∈ ({n + 2} : Finset ℕ), 2 ≤ k := by
      intro k hk
      simp only [Finset.mem_singleton] at hk
      omega
    have hp := n05_referenceHighProjection_outputRealization hab hpart hU hI
    simpa only [outputRemainder, zero_mul, sub_zero] using hp.2.1
  obtain ⟨hc, hsum, heq⟩ := n05_referenceHighAngularJet_weighted_sum hab hcell J b
    (fun m => Real.exp (-2 * M * radialQ (D.cellIndex m) +
      2 * γ * radialS (D.cellIndex m))) hs
  refine ⟨hc, hsum, ?_⟩
  simpa only [outputNormSquare, outputCellSquare, outputRemainder,
    n05_referenceHighOutputSquare, zero_mul, sub_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using heq

/-- The constant and the material exponents are fixed before the angular
order. This estimates actual derivatives of projections of the same G. -/
theorem n05_referenceInverse_finiteAngularJet_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ J : Finset ℕ, ∀ b : ℕ,
      outputNormSquare D γ M₁ 0 (n05_referenceHighAngularJet J b (G F).1, 0) ≤
        C ^ 2 * sourceNormSquare D γ M₀ (n05_referenceHighAngularJet J b F.1, 0) := by
  obtain ⟨C, hC, hbound⟩ := n05_referenceInverse_finiteAngularWeighted_bound hD hborder hγ hG
  refine ⟨C, hC, fun F hF J b => ?_⟩
  obtain ⟨a, hU⟩ := (hG.1 F hF).1
  rw [(n05_referenceHighAngularJet_output_norm hD hborder hγ hU J b).2.2,
    (n05_referenceHighAngularJet_source_norm hD hF J b).2]
  exact hbound F hF
    (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b))) (fun n => by positivity) J

end ContinuousFlexibility.Radial
