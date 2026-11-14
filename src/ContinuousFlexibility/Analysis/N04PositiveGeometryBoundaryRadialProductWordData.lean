import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryRadialProductComposition

/-!
# Fixed constants for radial product composition

Existential witnesses are selected with abstract scalar and plane
functions. The actual source height uses only the resulting fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

structure N04RadialProductCompositionWordData
    (E : Type*) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n N : ℕ) (L : ℝ) where
  C : ℝ
  one_le_C : 1 ≤ C
  bound :
    ∀ {U : Set E}, IsOpen U → ∀ c : ℝ,
      ∀ (f h : E × ℝ → PolarPoint → ℝ) (g : E × ℝ → PolarPoint → PolarPoint),
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (c, y.2)) →
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (h y) (g y (c, y.2))) →
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g y) (c, y.2)) →
      ∀ JF : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
        (fun y => radialBoundaryJet (f y) c j y.2),
      ∀ JH : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (h y) (g y (c, y.2))),
      ∀ JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → PolarPoint,
        SmoothDirections (U ×ˢ univ)
          (fun y => iteratedFDeriv ℝ j (g y) (c, y.2) v),
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun y => radialBoundaryJet (fun p => f y p * h y (g y p)) c n y.2),
      ∀ K s d, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ j hj, N04BoundaryWordBounds (JF j hj) K s d x θ P M H t shift) →
      (∀ j hj, N04BoundaryWordBounds (JH j hj) K s d x θ P M H t shift) →
      (∀ j hj hjn v, (∀ a, ‖v a‖ ≤ 1) →
        N04BoundaryWordBounds (JG j hj hjn v) K s d x θ P M H t shift) →
      N04BoundaryWordBounds Q K s d x θ P
        (C * M ^ ((n + 1 + 2 * N) * (N + 2))) H t shift

def n04PositiveGeometry_radialProductCompositionWordData
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n N : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    N04RadialProductCompositionWordData E n N L :=
  Classical.choice (by
    obtain ⟨C, hC, hbound⟩ :=
      n04PositiveGeometry_radialProductComposition_bound (E := E) n N L hL
    exact ⟨⟨C, hC, hbound⟩⟩)

end ContinuousFlexibility.Analysis
