import ContinuousFlexibility.Radial.MatchedPiecesAssembly

/-!
# The regional inner inverse before installing its fields

This is the exact output of the physical-to-frozen inverse construction.
It contains no Poisson columns or matrix estimate. The selected matching
shell has already fixed the physical cuts, frequency and source map.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

def SelectedTerminalInnerSupply {D : ReferenceData} (M : RadialMatchingData D)
    (cost : ℝ) : Prop :=
  ∃ A : RadialModePair D →L[ℝ] RadialModePair D,
  ∃ u : RadialModePair D → ℝ → ℝ,
    ‖A‖ ≤ cost ∧
    (∀ F, (M.frequency ≠ 2 → F.2 = 0) →
      ModeInnerDirichletGraph D M (A (M.sourceInner F)) (M.sourceInner F)) ∧
    (∀ U F, ModeInnerDirichletGraph D M U F → A F = U) ∧
    ∀ F, ((A (M.sourceInner F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u F ∧
      ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight)
        (A (M.sourceInner F)) (M.sourceInner F) ∧
      ContDiffOn ℝ 1 (u F) (Icc M.innerLeft M.innerRight) ∧
      (∀ r ∈ matchingOuterRegion D M, u F r = 0) ∧
      (if M.frequency = 2 then
        (∫ r in D.a..D.b, referenceColumn D r * u F r) = F.2
       else (A (M.sourceInner F)).2 = 0) ∧
      ∀ i, u F (matchingCut D M i) = 0

end ContinuousFlexibility.Radial
