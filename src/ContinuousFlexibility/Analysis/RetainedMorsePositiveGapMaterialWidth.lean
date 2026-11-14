import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapCoordinates
import ContinuousFlexibility.Analysis.ScaledMorsePositiveGapMaterialWidth

/-!
# Sampled width costs for the same retained positive gaps

The cell and index hypotheses of the scalar estimate are discharged by
the actual retained-coordinate certificate. The material datum and its
sample assignment stay fixed. This is a theorem about that same
constructed reference, not an extraction from arbitrary Through03.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- Any actual cell containing a point of the same scaled positive gap
controls its model weight; both root points are allowed. -/
theorem retainedReference_positive_gap_weight_bound
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (side : Bool) (n : ℕ), S.chain.index ≤ n →
      ∀ j r, r ∈ Icc (n06MorsePositiveLeft S.chain side n)
        (n06MorsePositiveRight S.chain side n) →
      P.sideRadius side * r ∈ Γ.reference.cells j →
        radialE (n + 1) ^ B ≤ C * T.E0 (T.sample j) ^ A := by
  obtain ⟨hcells, hindex⟩ := retainedReference_positive_gap_cell_transport
    P hS hband hcoordinates
  exact morseRealization_scaled_positive_gap_weight_bound
    (hS.2.2.2.1 S.sigma hS.2.2.1).1 hT hΓ.2.1
    P.sideRadius hcells hindex hB

/-- The actual positive-gap width has one uniform E0 inverse cost at
its physical midpoint sample. No optical root lower bound is needed. -/
theorem retainedReference_positive_gap_inverse_width_bound
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (side : Bool) (n : ℕ), S.chain.index ≤ n → ∀ j,
      P.sideRadius side * ((n06MorsePositiveLeft S.chain side n +
        n06MorsePositiveRight S.chain side n) / 2) ∈ Γ.reference.cells j →
      (P.sideRadius side * n06MorsePositiveRight S.chain side n -
        P.sideRadius side * n06MorsePositiveLeft S.chain side n)⁻¹ ≤
          C * T.E0 (T.sample j) ^ A := by
  obtain ⟨hcells, hindex⟩ := retainedReference_positive_gap_cell_transport
    P hS hband hcoordinates
  exact morseRealization_scaled_positive_gap_inverse_width_bound
    (hS.2.2.2.1 S.sigma hS.2.2.1).1 hS.2.2.1 hT hΓ.2.1
    P.sideRadius P.sideRadius_pos hcells hindex

end ContinuousFlexibility.Radial
