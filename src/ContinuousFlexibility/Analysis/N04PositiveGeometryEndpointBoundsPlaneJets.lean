module

public import ContinuousFlexibility.Analysis.N04RealizationPlaneJetDirections
public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryKernelBounds
public import ContinuousFlexibility.Analysis.RootUnitPhysicalJetTransfer
public import ContinuousFlexibility.Analysis.N06BoundaryRadialJets

/-!
# Finite plane evaluations and the original multilinear jets

Coordinate words recover the existing multilinear map and its genuine
parameter tower. Their bounds cost only the number of words. Fixed unit
root orientations preserve the complete ordered-word budget.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {U : Set X}

private def planeCoordinate (v : PolarPoint) (i : Fin 2) : ℝ :=
  if i = 0 then v.1 else v.2

private theorem planeCoordinate_norm_le (v : PolarPoint) (i : Fin 2) :
    ‖planeCoordinate v i‖ ≤ ‖v‖ := by
  unfold planeCoordinate
  split
  · exact norm_fst_le v
  · exact norm_snd_le v

private theorem plane_sum_coordinates (v : PolarPoint) :
    (∑ i : Fin 2, planeCoordinate v i • cylinderBasisVector i) = v := by
  rw [Fin.sum_univ_two]
  ext <;> simp [planeCoordinate, cylinderBasisVector]

private theorem planeBasis_expand {n : ℕ} (A : PolarPoint [×n]→L[ℝ] Y)
    (v : Fin n → PolarPoint) :
    A v = ∑ w : Fin n → Fin 2, (∏ i, planeCoordinate (v i) (w i)) •
      A (fun i => cylinderBasisVector (w i)) := by
  classical
  have hv : (fun i : Fin n => ∑ j : Fin 2,
      planeCoordinate (v i) j • cylinderBasisVector j) = v :=
    funext fun i => plane_sum_coordinates (v i)
  have he : A (fun i : Fin n => ∑ j : Fin 2,
      planeCoordinate (v i) j • cylinderBasisVector j) =
      ∑ w : Fin n → Fin 2, A (fun i => planeCoordinate (v i) (w i) •
        cylinderBasisVector (w i)) :=
    A.toMultilinearMap.map_sum
      (fun i : Fin n => fun j : Fin 2 => planeCoordinate (v i) j • cylinderBasisVector j)
  simpa only [hv, ContinuousMultilinearMap.map_smul_univ] using he

/-- Only the finitely many coordinate words are required to construct
the genuine tower of the original multilinear operator. -/
def n04PositiveGeometry_planeBasis_directions
    (n : ℕ) (A : X → PolarPoint [×n]→L[ℝ] Y)
    (J : ∀ w : Fin n → Fin 2,
      SmoothDirections U (fun x => A x (fun i => cylinderBasisVector (w i)))) :
    SmoothDirections U A := by
  classical
  apply n04Realization_planeMultilinear_directions n A
  intro v
  let Q (w : Fin n → Fin 2) := smoothDirections_postcompCLM (J w)
    ((∏ i, planeCoordinate (v i) (w i)) • ContinuousLinearMap.id ℝ Y)
  refine (smoothDirections_finiteSum (J (fun _ => 0)).open_domain Q).congr ?_
  intro x _
  simpa only [Function.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] using (planeBasis_expand (A x) v).symm

/-- A basis-word bound controls the norm in any normed codomain. -/
theorem n04PositiveGeometry_planeBasis_norm_le
    (n : ℕ) (A : PolarPoint [×n]→L[ℝ] Y) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ w : Fin n → Fin 2,
      ‖A (fun i => cylinderBasisVector (w i))‖ ≤ M) :
    ‖A‖ ≤ (2 : ℝ) ^ n * M := by
  classical
  refine A.opNorm_le_bound (by positivity) fun v => ?_
  rw [planeBasis_expand A v]
  calc
    ‖∑ w : Fin n → Fin 2, (∏ i, planeCoordinate (v i) (w i)) •
        A (fun i => cylinderBasisVector (w i))‖
        ≤ ∑ w : Fin n → Fin 2, ‖(∏ i, planeCoordinate (v i) (w i)) •
          A (fun i => cylinderBasisVector (w i))‖ := norm_sum_le _ _
    _ ≤ ∑ _w : Fin n → Fin 2, (∏ i, ‖v i‖) * M := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_smul, norm_prod]
      exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => planeCoordinate_norm_le (v i) (w i))) (h w)
        (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (2 : ℝ) ^ n * M * ∏ i, ‖v i‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- Finite evaluation bounds retain every state slot and angular reserve
of any genuine tower of the same operator. -/
theorem N04BoundaryWordBounds.of_planeBasis
    {n : ℕ} {A : X × ℝ → PolarPoint [×n]→L[ℝ] Y}
    (J : SmoothDirections (U ×ˢ univ) A)
    (Q : ∀ c : Fin n → Fin 2, SmoothDirections (U ×ˢ univ)
      (fun y => A y (fun i => cylinderBasisVector (c i))))
    {K s d : ℕ} {x : X} (hx : x ∈ U) {θ : ℝ} {P : X → Prop}
    {M H t : ℝ} {shift : ℕ} (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (h : ∀ c, N04BoundaryWordBounds (Q c) K s d x θ P M H t shift) :
    N04BoundaryWordBounds J K s d x θ P ((2 : ℝ) ^ n * M) H t shift := by
  intro N w hk ha v hv hp
  have hnonneg : 0 ≤ M * parameterHeightWeight H w.stateArity *
      t ^ ((w.angleArity - d) + shift * w.stateArity) :=
    mul_nonneg (mul_nonneg hM (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _)
  have hb (c : Fin n → Fin 2) :
      ‖(J.D N (x, θ) v) (fun i => cylinderBasisVector (c i))‖ ≤
        M * parameterHeightWeight H w.stateArity *
          t ^ ((w.angleArity - d) + shift * w.stateArity) := by
    let L : (PolarPoint [×n]→L[ℝ] Y) →L[ℝ] Y :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => PolarPoint) Y
        (fun i => cylinderBasisVector (c i))
    let JE : SmoothDirections (U ×ˢ univ)
        (fun y => A y (fun i => cylinderBasisVector (c i))) :=
      (smoothDirections_postcompCLM J L).congr (fun y _ => by
        simp only [Function.comp_apply, L, ContinuousMultilinearMap.apply_apply])
    have he := congrArg (fun T : (X × ℝ) [×N]→L[ℝ] Y => T v)
      (JE.unique (Q c) N (x, θ) ⟨hx, mem_univ _⟩)
    have he' : (J.D N (x, θ) v) (fun i => cylinderBasisVector (c i)) =
        (Q c).D N (x, θ) v := by
      simpa only [JE, SmoothDirections.congr, smoothDirections_postcompCLM_D_apply,
        L, ContinuousMultilinearMap.apply_apply] using he
    exact (congrArg norm he').trans_le (h c N w hk ha v hv hp)
  simpa only [mul_assoc] using
    n04PositiveGeometry_planeBasis_norm_le n (J.D N (x, θ) v) hnonneg hb

def n04PositiveGeometry_planePrecomp_directions
    (n : ℕ) (A : X → PolarPoint [×n]→L[ℝ] Y) (J : SmoothDirections U A)
    (L : PolarPoint →L[ℝ] PolarPoint) :
    SmoothDirections U (fun x => (A x).compContinuousLinearMap (fun _ => L)) :=
  (smoothDirections_postcompCLM J
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => L))).congr
    (fun x _ => by
      simp only [Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapL_apply])

theorem n04PositiveGeometry_planePrecomp_norm_le_one
    (n : ℕ) (L : PolarPoint →L[ℝ] PolarPoint) (hL : ‖L‖ ≤ 1) :
    ‖(ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => L) :
      (PolarPoint [×n]→L[ℝ] Y) →L[ℝ] (PolarPoint [×n]→L[ℝ] Y))‖ ≤ 1 := by
  have h : ‖(ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => L) :
      (PolarPoint [×n]→L[ℝ] Y) →L[ℝ] (PolarPoint [×n]→L[ℝ] Y))‖ ≤ ‖L‖ ^ n := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      ContinuousMultilinearMap.norm_compContinuousLinearMapL_le Y (fun _ : Fin n => L)
  exact h.trans ((pow_le_pow_left₀ (norm_nonneg L) hL n).trans_eq (one_pow n))

theorem N04BoundaryWordBounds.planePrecomp
    {n : ℕ} {A : X × ℝ → PolarPoint [×n]→L[ℝ] Y}
    {J : SmoothDirections (U ×ˢ univ) A}
    {K s d : ℕ} {x : X} {θ : ℝ} {P : X → Prop} {M H t : ℝ} {shift : ℕ}
    (h : N04BoundaryWordBounds J K s d x θ P M H t shift) (hx : x ∈ U)
    (L : PolarPoint →L[ℝ] PolarPoint) (hL : ‖L‖ ≤ 1)
    (Q : SmoothDirections (U ×ˢ univ)
      (fun y => (A y).compContinuousLinearMap (fun _ => L))) :
    N04BoundaryWordBounds Q K s d x θ P M H t shift := by
  let T : (PolarPoint [×n]→L[ℝ] Y) →L[ℝ] (PolarPoint [×n]→L[ℝ] Y) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => L)
  have hb := h.postcompCLM T (n04PositiveGeometry_planePrecomp_norm_le_one n L hL)
  exact hb.congr (Q := Q) hx (fun y _ => by
    simp only [Function.comp_apply, T, ContinuousMultilinearMap.compContinuousLinearMapL_apply])

theorem N04BoundaryWordBounds.planeUnscale
    {n : ℕ} {A : X × ℝ → PolarPoint [×n]→L[ℝ] Y}
    {J : SmoothDirections (U ×ˢ univ) A}
    {K s d : ℕ} {x : X} {θ σ : ℝ} {P : X → Prop} {M H t : ℝ} {shift : ℕ}
    (h : N04BoundaryWordBounds J K s d x θ P M H t shift) (hx : x ∈ U)
    (hσ : σ = 1 ∨ σ = -1)
    (Q : SmoothDirections (U ×ˢ univ)
      (fun y => (A y).compContinuousLinearMap (fun _ => rootProfileInverseLinear σ))) :
    N04BoundaryWordBounds Q K s d x θ P M H t shift :=
  h.planePrecomp hx (rootProfileInverseLinear σ) (norm_rootProfileInverseLinear_unit hσ).le Q

/-- The complete original spatial jet is the shifted jet composed with
the fixed inverse radial linear map. No joint model regularity is used. -/
theorem n04PositiveGeometry_rootProfileJet_unscale
    (r σ θ : ℝ) (hσ : σ ≠ 0) (F : PolarPoint → Y) (n : ℕ)
    (hf : ContDiffAt ℝ ∞ (fun p => F (rootProfileShift r σ p)) (0, θ)) :
    iteratedFDeriv ℝ n F (r, θ) =
      (iteratedFDeriv ℝ n (fun p => F (rootProfileShift r σ p)) (0, θ)).compContinuousLinearMap
        (fun _ => rootProfileInverseLinear σ) := by
  let a : PolarPoint := (-r / σ, 0)
  let L : PolarPoint →L[ℝ] PolarPoint := rootProfileInverseLinear σ
  let G : PolarPoint → Y := fun p => F (rootProfileShift r σ p)
  have hback (y : PolarPoint) : rootProfileShift r σ (a + L y) = y := by
    ext <;> simp only [a, L, rootProfileInverseLinear, rootProfileShift,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd, smul_eq_mul, zero_add] <;>
      field_simp [hσ] <;> ring
  have harg : a + L (r, θ) = (0, θ) := by
    ext <;> simp only [a, L, rootProfileInverseLinear,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd, smul_eq_mul, zero_add] <;>
      field_simp [hσ] <;> ring
  have hG : ContDiffAt ℝ ∞ G (a + L (r, θ)) := by
    rw [harg]
    exact hf
  have hshift : ContDiffAt ℝ (n : ℕ∞ω) (fun y => G (a + y)) (L (r, θ)) :=
    (hG.of_le (by simp)).comp _ (contDiffAt_const.add contDiffAt_id)
  have he := n06_iteratedFDeriv_compCLM_at L (x := (r, θ)) n hshift
  rw [iteratedFDeriv_comp_add_left, harg] at he
  have hfun : (fun y => G (a + y)) ∘ L = F := by
    funext y
    simp only [Function.comp_apply, G, hback]
  rw [hfun] at he
  exact he

end ContinuousFlexibility.Analysis
