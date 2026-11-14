module

public import ContinuousFlexibility.Blueprint.Statements

/-!
# Assembling the two regions of one matching datum

The predicates below partition the clauses of MatchingLocalRealizations
between the inner and outer constructions. They use the same existing
RadialMatchingData; in particular, the cuts, frequencies, source maps,
normalizations and boundary matrices are shared.

The equivalence only rearranges the actual graph, representative, equation
and boundary clauses. It constructs neither a geometry nor a local inverse.
The final helper adds the numerical matching clauses to these two outputs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- All inner-region clauses, with the actual scalar border coordinate. -/
def MatchingInnerRealizations (D : ReferenceData) (M : RadialMatchingData D) : Prop :=
  (∀ F, (M.frequency ≠ 2 → F.2 = 0) →
    ModeInnerDirichletGraph D M (M.innerInverse (M.sourceInner F)) (M.sourceInner F)) ∧
  (∀ U F, ModeInnerDirichletGraph D M U F → M.innerInverse F = U) ∧
  (∀ F, (M.sourceInner F).2 = F.2 ∧
    ((M.sourceInner F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => if r ∈ Ioo M.innerLeft M.innerRight then F.1 r else 0)) ∧
  (∀ F,
    ((M.innerInverse (M.sourceInner F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      M.innerRepresentative F ∧
    ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight)
      (M.innerInverse (M.sourceInner F)) (M.sourceInner F) ∧
    ContDiffOn ℝ 1 (M.innerRepresentative F) (Icc M.innerLeft M.innerRight) ∧
    (∀ r ∈ matchingOuterRegion D M, M.innerRepresentative F r = 0) ∧
    (if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * M.innerRepresentative F r) = F.2
     else (M.innerInverse (M.sourceInner F)).2 = 0) ∧
    (∀ i, M.innerRepresentative F (matchingCut D M i) = 0)) ∧
  (∀ i,
    ((M.innerPoisson i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] M.innerFunction i ∧
    ((M.innerPoisson i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] (fun _ => 0) ∧
    ContDiffOn ℝ 2 (M.innerFunction i) (Icc M.innerLeft M.innerRight) ∧
    ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (M.innerPoisson i) 0 ∧
    (if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * M.innerFunction i r) = 0
     else (M.innerPoisson i).2 = 0) ∧
    (∀ k, M.innerFunction i (matchingCut D M k) = (if i = k then 1 else 0) /
        sqrt (M.boundaryScale k) ∧
      M.Db k i = matchingInnerFlux D M (M.innerFunction i) k))

/-- All outer-region clauses, including the natural separated graph and
the actual diagonal Robin conditions at the shared cuts. -/
def MatchingOuterRealizations (D : ReferenceData) (M : RadialMatchingData D) : Prop :=
  (∀ F, (M.frequency ≠ 2 → F.2 = 0) →
    ModeOuterSeparatedGraph D M (M.outerInverse (M.sourceOuter F)) (M.sourceOuter F)) ∧
  (∀ U F, ModeOuterSeparatedGraph D M U F → M.outerInverse F = U) ∧
  (∀ F, (M.sourceOuter F).2 = 0 ∧
    ((M.sourceOuter F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => if r ∈ Ioo M.innerLeft M.innerRight then 0 else F.1 r)) ∧
  (∀ F,
    ((M.outerInverse (M.sourceOuter F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      M.outerRepresentative F ∧
    ModeLocalEquation D M.frequency (matchingOuterRegion D M)
      (M.outerInverse (M.sourceOuter F)) (M.sourceOuter F) ∧
    ContDiffOn ℝ 1 (M.outerRepresentative F)
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
    (∀ r ∈ Ioo M.innerLeft M.innerRight, M.outerRepresentative F r = 0) ∧
    (M.outerInverse (M.sourceOuter F)).2 = 0 ∧
    (∀ i, M.A i i * sqrt (M.boundaryScale i) *
      M.outerRepresentative F (matchingCut D M i) +
      M.B i i * matchingOuterFlux D M (M.outerRepresentative F) i = 0)) ∧
  (∀ i,
    ((M.outerPoisson i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] M.outerFunction i ∧
    ((M.outerPoisson i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] (fun _ => 0) ∧
    ContDiffOn ℝ 2 (M.outerFunction i)
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
    (M.outerPoisson i).2 = 0 ∧
    ModeLocalEquation D M.frequency (matchingOuterRegion D M) (M.outerPoisson i) 0 ∧
    (∀ k, M.outerFunction i (matchingCut D M k) = M.A k i / sqrt (M.boundaryScale k) ∧
      matchingOuterFlux D M (M.outerFunction i) k = M.B k i))

variable {D : ReferenceData} {M : RadialMatchingData D}

theorem matchingInnerRealizations_of_local (h : MatchingLocalRealizations D M) :
    MatchingInnerRealizations D M := by
  rcases h with ⟨hsolve, huniq, _, hsource, hrep, hpoisson⟩
  refine ⟨fun F hF => (hsolve F hF).1, huniq, ?_, ?_, ?_⟩
  · intro F
    exact ⟨(hsource F).1, (hsource F).2.2.1⟩
  · intro F
    rcases hrep F with ⟨hia, hoa, hie, hoe, hir, hor, hiz, hoz, hirow, hos, hib, hob⟩
    exact ⟨hia, hie, hir, hiz, hirow, hib⟩
  · intro i
    rcases hpoisson i with ⟨hia, hoa, hiz, hoz, hir, hor, hos, hie, hoe, hirow, hb⟩
    exact ⟨hia, hiz, hir, hie, hirow, fun k => ⟨(hb k).1, (hb k).2.1⟩⟩

theorem matchingOuterRealizations_of_local (h : MatchingLocalRealizations D M) :
    MatchingOuterRealizations D M := by
  rcases h with ⟨hsolve, _, huniq, hsource, hrep, hpoisson⟩
  refine ⟨fun F hF => (hsolve F hF).2, huniq, ?_, ?_, ?_⟩
  · intro F
    exact ⟨(hsource F).2.1, (hsource F).2.2.2⟩
  · intro F
    rcases hrep F with ⟨hia, hoa, hie, hoe, hir, hor, hiz, hoz, hirow, hos, hib, hob⟩
    exact ⟨hoa, hoe, hor, hoz, hos, hob⟩
  · intro i
    rcases hpoisson i with ⟨hia, hoa, hiz, hoz, hir, hor, hos, hie, hoe, hirow, hb⟩
    exact ⟨hoa, hoz, hor, hos, hoe, fun k => ⟨(hb k).2.2.1, (hb k).2.2.2⟩⟩

/-- Joining the two region outputs preserves every frozen local clause. -/
theorem matchingLocalRealizations_of_regions
    (hinner : MatchingInnerRealizations D M) (houter : MatchingOuterRealizations D M) :
    MatchingLocalRealizations D M := by
  rcases hinner with ⟨hsi, hui, hfi, hri, hpi⟩
  rcases houter with ⟨hso, huo, hfo, hro, hpo⟩
  refine ⟨fun F hF => ⟨hsi F hF, hso F hF⟩, hui, huo, ?_, ?_, ?_⟩
  · intro F
    exact ⟨(hfi F).1, (hfo F).1, (hfi F).2, (hfo F).2⟩
  · intro F
    rcases hri F with ⟨hia, hie, hir, hiz, hirow, hib⟩
    rcases hro F with ⟨hoa, hoe, hor, hoz, hos, hob⟩
    exact ⟨hia, hoa, hie, hoe, hir, hor, hiz, hoz, hirow, hos, hib, hob⟩
  · intro i
    rcases hpi i with ⟨hia, hiz, hir, hie, hirow, hib⟩
    rcases hpo i with ⟨hoa, hoz, hor, hos, hoe, hob⟩
    exact ⟨hia, hoa, hiz, hoz, hir, hor, hos, hie, hoe, hirow,
      fun k => ⟨(hib k).1, (hib k).2, (hob k).1, (hob k).2⟩⟩

theorem matchingLocalRealizations_iff_regions :
    MatchingLocalRealizations D M ↔
      MatchingInnerRealizations D M ∧ MatchingOuterRealizations D M :=
  ⟨fun h => ⟨matchingInnerRealizations_of_local h, matchingOuterRealizations_of_local h⟩,
    fun h => matchingLocalRealizations_of_regions h.1 h.2⟩

/-- The same matching datum acquires MatchedPieces once the geometry,
selected margin and numerical matrix bounds accompany its two regions. -/
theorem matchedPieces_of_regions
    (hcuts : D.a < M.innerLeft ∧ M.innerLeft < M.innerRight ∧ M.innerRight < D.b)
    (hsupport : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (hmargin : 0 < M.margin)
    (hdiagonal : ∀ i, 0 < M.boundaryScale i ∧ 0 < M.D0 i ∧ M.D0 i ≤ 1 / 2 ∧
      M.margin ≤ |M.A i i * M.D0 i - M.B i i|)
    (herror : ∀ i j, |M.Db i j - (if i = j then M.D0 i else 0)| ≤ M.margin / 16)
    (hinner : MatchingInnerRealizations D M) (houter : MatchingOuterRealizations D M)
    (hsymmetric : ∀ i j, M.Db i j = M.Db j i)
    (hoffdiagonal : ∀ i j, i ≠ j → M.A i j = 0 ∧ M.B i j = 0)
    (hnormalized : ∀ i, M.A i i ^ 2 + M.B i i ^ 2 = 1) :
    Blueprint.MatchedPieces D M :=
  ⟨hcuts.1, hcuts.2.1, hcuts.2.2, hsupport, hmargin, hdiagonal, herror,
    matchingLocalRealizations_of_regions hinner houter, hsymmetric, hoffdiagonal, hnormalized⟩

end ContinuousFlexibility.Radial
