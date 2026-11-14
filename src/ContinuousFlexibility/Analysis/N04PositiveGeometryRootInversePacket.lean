module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseLinearBounds

/-!
# The abstract scalar packet for an inverse root differential

All moving-point and word calculations are performed with four opaque
scalar functions. The actual root formulas enter only through a later
pointwise equality, so these calculations do not unfold a state chart.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

def n04PositiveGeometry_rootInversePacket (σ c : ℝ) (o e b ψ : E × ℝ → ℝ)
    (y : E × ℝ) : PolarPoint →L[ℝ] PolarPoint :=
  n04PositiveGeometry_rootInverseLinear σ (c * o (y.1, ψ y)) (e (y.1, ψ y)) (b y)

def n04PositiveGeometry_rootInversePacket_joint
    {U : Set E} {o e b ψ : E × ℝ → ℝ} (σ c : ℝ)
    (JO : SmoothDirections (U ×ˢ univ) o)
    (JE : SmoothDirections (U ×ˢ univ) e)
    (Jb : SmoothDirections (U ×ˢ univ) b)
    (Jψ : SmoothDirections (U ×ˢ univ) ψ) :
    SmoothDirections (U ×ˢ univ) (n04PositiveGeometry_rootInversePacket σ c o e b ψ) := by
  let Ja : SmoothDirections (U ×ˢ univ) (fun y => c * o y) :=
    smoothDirections_postcompCLM JO (c • ContinuousLinearMap.id ℝ ℝ)
  let Jam : SmoothDirections (U ×ˢ univ) (fun y => c * o (y.1, ψ y)) :=
    n04PositiveGeometry_boundaryMoving_directions Ja Jψ
  let Jem : SmoothDirections (U ×ˢ univ) (fun y => e (y.1, ψ y)) :=
    n04PositiveGeometry_boundaryMoving_directions JE Jψ
  exact n04PositiveGeometry_rootInverseLinear_directions σ Jam Jem Jb

theorem n04PositiveGeometry_rootInversePacket_word_bound
    (K s : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ degree : ℕ, 1 ≤ degree ∧
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
      (A * M ^ degree) H t (shift + 1) := by
  obtain ⟨A, hA, degree, hd, hbound⟩ :=
    n04PositiveGeometry_rootInverseMoving_word_bound (E := E) K s L hL
  refine ⟨A, hA, degree, hd, ?_⟩
  intro U hU o e b ψ JO JE Jb Jψ σ hσ c hc Q x hx θ p q R hR M H t
    hM hH hHM hHL ht shift hO hE hψ hb
  let Ja : SmoothDirections (U ×ˢ univ) (fun y => c * o y) :=
    smoothDirections_postcompCLM JO (c • ContinuousLinearMap.id ℝ ℝ)
  let Jam : SmoothDirections (U ×ˢ univ) (fun y => c * o (y.1, ψ y)) :=
    n04PositiveGeometry_boundaryMoving_directions Ja Jψ
  let Jem : SmoothDirections (U ×ˢ univ) (fun y => e (y.1, ψ y)) :=
    n04PositiveGeometry_boundaryMoving_directions JE Jψ
  have ha : N04BoundaryWordBounds Ja K (s + K) 1 x (ψ (x, θ))
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift :=
    (hO.scale c).enlarge hH (zero_le_one.trans ht)
      ((mul_le_mul_of_nonneg_right hc (zero_le_one.trans hM)).trans_eq (one_mul M))
  exact hbound hU Ja JE Jb Jψ Jam Jem σ hσ Q
    x hx θ p q R hR M H t hM hH hHM hHL ht shift ha hE hψ hb

end ContinuousFlexibility.Analysis
