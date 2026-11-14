module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryTraceOperations
public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPlaneJets
public import ContinuousFlexibility.Analysis.N01cFiniteParameterProducts

/-! # Fixed output projections of actual plane multilinear jets -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E F G : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set E} {n : ℕ} {f : E × ℝ → PolarPoint [×n]→L[ℝ] F}

def n04PositiveGeometry_planePostcomp_directions
    (J : SmoothDirections (U ×ˢ univ) f) (L : F →L[ℝ] G) :
    SmoothDirections (U ×ˢ univ) (fun y => L.compContinuousMultilinearMap (f y)) := by
  apply n04PositiveGeometry_planeBasis_directions n
  intro w
  exact smoothDirections_postcompCLM
    (n04PositiveGeometry_boundaryFixedEvaluation_directions J
      (fun i => cylinderBasisVector (w i))) L

theorem N04BoundaryWordBounds.planePostcomp
    {J : SmoothDirections (U ×ˢ univ) f}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (hb : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (hx : x ∈ U) (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    (Q : SmoothDirections (U ×ˢ univ) (fun y => L.compContinuousMultilinearMap (f y))) :
    N04BoundaryWordBounds Q K s d x θ P ((2 : ℝ) ^ n * M) H t shift := by
  let JE (w : Fin n → Fin 2) := smoothDirections_postcompCLM
    (n04PositiveGeometry_boundaryFixedEvaluation_directions J
      (fun i => cylinderBasisVector (w i))) L
  have hunit (a : Fin 2) : ‖cylinderBasisVector a‖ ≤ 1 := by
    fin_cases a <;> norm_num [cylinderBasisVector, Prod.norm_def]
  apply N04BoundaryWordBounds.of_planeBasis Q JE hx hM hH ht
  intro w
  exact (hb.fixedEvaluation (fun i => cylinderBasisVector (w i))
    (fun i => hunit (w i))).postcompCLM L hL

theorem n04PositiveGeometry_boundaryWord_constant
    (c : ℝ) (Q : SmoothDirections (U ×ˢ univ) (fun _ : E × ℝ => c))
    (K s d : ℕ) (x : E) (hx : x ∈ U) (θ : ℝ) (P : E → Prop)
    (M H t : ℝ) (shift : ℕ) (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hc : |c| ≤ M) : N04BoundaryWordBounds Q K s d x θ P M H t shift := by
  intro n w _ _ v _ _
  by_cases hn : n = 0
  · subst n
    have he := smoothDirections_D_zero_apply Q (x := (x, θ)) ⟨hx, mem_univ θ⟩ v
    have hk : w.stateArity = 0 := by have h := w.arity_sum; omega
    have ha : w.angleArity = 0 := by have h := w.arity_sum; omega
    simpa only [he, Real.norm_eq_abs, hk, ha, parameterHeightWeight, ite_true,
      Nat.zero_sub, Nat.mul_zero, Nat.zero_add, pow_zero, mul_one] using hc
  · have he := smoothDirections_D_constant Q (Nat.pos_of_ne_zero hn)
      (x := (x, θ)) ⟨hx, mem_univ θ⟩ v
    exact (congrArg norm he).trans_le (by
      simpa only [norm_zero] using mul_nonneg
        (mul_nonneg hM (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _))

def n04PositiveGeometry_angleOutputProjection : PolarPoint →L[ℝ] PolarPoint :=
  (0 : PolarPoint →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem n04PositiveGeometry_angleOutputProjection_apply (p : PolarPoint) :
    n04PositiveGeometry_angleOutputProjection p = (0, p.2) := rfl

theorem n04PositiveGeometry_angleOutputProjection_norm :
    ‖n04PositiveGeometry_angleOutputProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simpa only [n04PositiveGeometry_angleOutputProjection_apply, Prod.norm_def,
    norm_zero, max_eq_right (norm_nonneg p.2), one_mul] using norm_snd_le p

end ContinuousFlexibility.Analysis
