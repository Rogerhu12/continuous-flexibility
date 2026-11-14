module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryMultilinearKernel

/-!
# Actual boundary operator evaluation with angular reserves

These finite kernel consumers keep both the original state arity and
the reserved angular order. They apply to genuine operator towers,
including the operators in the actual finite inverse recurrence.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X E F : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem n04PositiveGeometry_boundary_multilinearApply_bound (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {U : Set X} {A : X × ℝ → E [×n]→L[ℝ] F}
        {v : X × ℝ → Fin n → E},
      ∀ JA : SmoothDirections (U ×ˢ univ) A,
      ∀ JV : SmoothDirections (U ×ˢ univ) v,
      ∀ Q : SmoothDirections (U ×ˢ univ) (fun z => A z (v z)),
      ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
      N04BoundaryWordBounds JA K s d x θ P M H t shift →
      N04BoundaryWordBounds JV K s d x θ P M H t shift →
      N04BoundaryWordBounds Q K s d x θ P
        (C * M ^ (n + 1 + 2 * N)) H t shift := by
  obtain ⟨A, hA, ha⟩ := n04PositiveGeometry_multilinearEvaluation_prefix (E := E) (F := F) n N
  obtain ⟨C, hC, hc⟩ := n04PositiveGeometry_boundaryKernel_polynomial_bound (E := X)
    (F := (E [×n]→L[ℝ] F) × (Fin n → E)) (G := F) N (n + 1) A hA
  refine ⟨C, hC, ?_⟩
  intro U A v JA JV Q K s d hN x hx θ P M H t hM hH hHM ht shift hJA hJV
  let J := smoothDirectionsProd JA JV
  have hJ : N04BoundaryWordBounds J K s d x θ P M H t shift := hJA.prod hJV
  exact hc (g := fun p : (E [×n]→L[ℝ] F) × (Fin n → E) => p.1 p.2)
    J Q isOpen_univ (contDiff_multilinearEvaluation n).contDiffOn
    (fun _ _ => mem_univ _) K s d hN x hx θ P M H t hM hH hHM ht shift hJ
    (fun j hj => ha M hM (A (x, θ), v (x, θ)) (hJ.value hx) j hj)

theorem n04PositiveGeometry_boundary_negClmApply_bound (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {U : Set X} {A : X × ℝ → E →L[ℝ] F} {v : X × ℝ → E},
      ∀ JA : SmoothDirections (U ×ˢ univ) A,
      ∀ JV : SmoothDirections (U ×ˢ univ) v,
      ∀ Q : SmoothDirections (U ×ˢ univ) (fun z => -A z (v z)),
      ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
      N04BoundaryWordBounds JA K s d x θ P M H t shift →
      N04BoundaryWordBounds JV K s d x θ P M H t shift →
      N04BoundaryWordBounds Q K s d x θ P
        (C * M ^ (2 + 2 * N)) H t shift := by
  obtain ⟨C, hC, hc⟩ := n04PositiveGeometry_boundaryKernel_polynomial_bound (E := X)
    (F := (E →L[ℝ] F) × E) (G := F) N 2 ((2 : ℝ) ^ N)
    (one_le_pow₀ (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro U A v JA JV Q K s d hN x hx θ P M H t hM hH hHM ht shift hJA hJV
  let J := smoothDirectionsProd JA JV
  have hJ : N04BoundaryWordBounds J K s d x θ P M H t shift := hJA.prod hJV
  exact hc (g := fun p : (E →L[ℝ] F) × E => -p.1 p.2)
    J Q isOpen_univ (contDiff_fst.clm_apply contDiff_snd).neg.contDiffOn
    (fun _ _ => mem_univ _) K s d hN x hx θ P M H t hM hH hHM ht shift hJ
    (fun j hj => n04PositiveGeometry_negClmEvaluation_prefix N hM
      (A (x, θ), v (x, θ)) (hJ.value hx) j hj)

end ContinuousFlexibility.Analysis
