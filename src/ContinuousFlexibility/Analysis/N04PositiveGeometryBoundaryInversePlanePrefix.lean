import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryInversePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPlaneJets

/-! # Full plane inverse jets from the finite evaluated prefix -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04PositiveGeometry_boundaryInverse_plane_prefix_bound (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ, 1 ≤ degree ∧
    ∀ {U : Set X}, IsOpen U →
    ∀ (f g : X × ℝ → PolarPoint → PolarPoint)
      (q : X × ℝ → PolarPoint) (L : X × ℝ → PolarPoint →L[ℝ] PolarPoint),
    (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (g y (q y))) →
    (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g y) (q y)) →
    (∀ y ∈ U ×ˢ univ, f y ∘ g y =ᶠ[𝓝 (q y)] (id : PolarPoint → PolarPoint)) →
    (∀ y ∈ U ×ˢ univ,
      (L y).comp (fderiv ℝ (f y) (g y (q y))) = ContinuousLinearMap.id ℝ PolarPoint) →
    ∀ JL : SmoothDirections (U ×ˢ univ) L,
    ∀ JF : ∀ j, 2 ≤ j → j ≤ 4 →
      SmoothDirections (U ×ˢ univ) (fun y => iteratedFDeriv ℝ j (f y) (g y (q y))),
    ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift : ℕ,
    N04BoundaryWordBounds JL K s d x θ P M H t shift →
    (∀ j hj hj4, N04BoundaryWordBounds (JF j hj hj4) K s d x θ P M H t shift) →
    ∀ j : ℕ, 1 ≤ j → j ≤ 4 →
    ∀ Q : SmoothDirections (U ×ˢ univ) (fun y => iteratedFDeriv ℝ j (g y) (q y)),
    N04BoundaryWordBounds Q K s d x θ P (C * M ^ degree) H t shift := by
  obtain ⟨C, hC, degree, hd, hbound⟩ :=
    n04PositiveGeometry_boundaryInverse_prefix_bound (X := X) (E := PolarPoint) (F := PolarPoint) N 4
  refine ⟨16 * C, one_le_mul_of_one_le_of_one_le (by norm_num) hC, degree, hd, ?_⟩
  intro U hU f g q L hf hg hfg hL JL JF K s d hN x hx θ P M H t hM hH hHM ht shift hJL hJF j hj hj4 Q
  let JE (w : Fin j → Fin 2) : SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ j (g y) (q y) (fun i => cylinderBasisVector (w i))) :=
    (smoothDirections_postcompCLM Q
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => PolarPoint) PolarPoint
        (fun i => cylinderBasisVector (w i)))).congr
      (fun _ _ => by simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply])
  have hbasis (a : Fin 2) : ‖cylinderBasisVector a‖ ≤ 1 := by
    fin_cases a <;> norm_num [cylinderBasisVector, Prod.norm_def]
  have hJE (w : Fin j → Fin 2) := hbound hU f g q L hf hg hfg hL JL JF
    K s d hN x hx θ P M H t hM hH hHM ht shift hJL hJF j hj hj4
    (fun i => cylinderBasisVector (w i)) (fun i => hbasis (w i)) (JE w)
  have hout := N04BoundaryWordBounds.of_planeBasis Q JE hx
    (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hM) _))
    hH (zero_le_one.trans ht) hJE
  apply hout.enlarge hH (zero_le_one.trans ht)
  have htwo : (2 : ℝ) ^ j ≤ 16 :=
    (pow_le_pow_right₀ (by norm_num) hj4).trans_eq (by norm_num)
  exact (mul_le_mul_of_nonneg_right htwo
    (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hM) _))).trans_eq (by ring)

end ContinuousFlexibility.Analysis
