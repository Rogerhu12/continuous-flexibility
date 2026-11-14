module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInversePacket

/-!
# Fixed constants for inverse packet word bounds

The witnesses are selected while the parameter space and all four scalar
functions are abstract. Actual root charts consume fields of this data,
without eliminating an existential into their full quantitative target.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

structure N04RootInversePacketWordData
    (E : Type*) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (K s : ℕ) (L : ℝ) where
  A : ℝ
  degree : ℕ
  one_le_A : 1 ≤ A
  one_le_degree : 1 ≤ degree
  bound :
    ∀ {U : Set E}, IsOpen U → ∀ {o e b ψ : E × ℝ → ℝ},
    ∀ JO : SmoothDirections (U ×ˢ univ) o,
    ∀ JE : SmoothDirections (U ×ˢ univ) e,
    ∀ Jb : SmoothDirections (U ×ˢ univ) b,
    ∀ Jψ : SmoothDirections (U ×ˢ univ) ψ,
    ∀ σ : ℝ, σ = 1 ∨ σ = -1 → ∀ c : ℝ, |c| ≤ 1 →
    ∀ Q : SmoothDirections (U ×ˢ univ) (n04PositiveGeometry_rootInversePacket σ c o e b ψ),
    ∀ x ∈ U, ∀ θ, ∀ p q : Seminorm ℝ E, ∀ R : ℝ, 0 ≤ R →
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → H ≤ L → 1 ≤ t → ∀ shift : ℕ,
    N04BoundaryWordBounds JO K (s + K) 1 x (ψ (x, θ))
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryWordBounds JE K (s + K) 1 x (ψ (x, θ))
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryPositiveWordBounds Jψ K (s + K) 1 x θ
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryWordBounds Jb K s 1 x θ
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryWordBounds Q K s 1 x θ (fun v => p v ≤ 1 ∧ q v ≤ R)
      (A * M ^ degree) H t (shift + 1)

def n04PositiveGeometry_rootInversePacketWordData
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (K s : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    N04RootInversePacketWordData E K s L :=
  Classical.choice (by
    obtain ⟨A, hA, degree, hd, hbound⟩ :=
      n04PositiveGeometry_rootInversePacket_word_bound (E := E) K s L hL
    exact ⟨⟨A, degree, hA, hd, hbound⟩⟩)

end ContinuousFlexibility.Analysis
