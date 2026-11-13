import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledSavedMovingWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryKernelBounds
import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# Boundary towers at the actual moving angle

The moving variable is the real angle. The state retains its original
topology, and the outer target may be a space of continuous multilinear
maps. A finite angular horizon pays for parameter slots becoming angle
slots. No absolute bound is imposed on the unwrapped inner angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The boundary budget restricted to positive ordinary orders. In
particular, it places no condition on the value of an angular lift. -/
def N04BoundaryPositiveWordBounds
    {U : Set E} {f : E × ℝ → F}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (K s d : ℕ) (x : E) (θ : ℝ) (P : E → Prop)
    (M H t : ℝ) (shift : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ w : StateAngleWord n,
    w.stateArity ≤ K → w.angleArity ≤ s + d →
    ∀ v : Fin n → E × ℝ, w.IsPure v → (∀ i, P (v i).1) →
      ‖J.D n (x, θ) v‖ ≤ M * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - d) + shift * w.stateArity)

theorem N04BoundaryWordBounds.positive
    {U : Set E} {f : E × ℝ → F}
    {J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop}
    {M H t : ℝ} {shift : ℕ}
    (h : N04BoundaryWordBounds J K s d x θ P M H t shift) :
    N04BoundaryPositiveWordBounds J K s d x θ P M H t shift :=
  fun n _ => h n

/-- The genuine composition on the original state domain. Only the
intermediate locally convex structure and completeness of the normed
target are needed. -/
def n04PositiveGeometry_boundaryMoving_directions
    [LocallyConvexSpace ℝ E] [CompleteSpace F]
    {U : Set E} {f : E × ℝ → F} {ψ : E × ℝ → ℝ}
    (JF : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (Jψ : SmoothDirections (U ×ˢ (univ : Set ℝ)) ψ) :
    SmoothDirections (U ×ˢ (univ : Set ℝ)) (fun p => f (p.1, ψ p)) := by
  let e := constEquiv F
  let KP := smoothDirections_postcompCLM JF e.toContinuousLinearMap
  let CP := smoothDirectionsUniformCompGeneric (smoothDirections_stateFlowGraph Jψ) KP
    (fun p hp => ⟨hp.1, mem_univ _⟩)
  let Q := smoothDirections_postcompCLM CP e.symm.toContinuousLinearMap
  exact Q.congr (fun p _ => e.symm_apply_apply (f (p.1, ψ p)))

private theorem boundary_pure_unit_bound
    {n : ℕ} (w : StateAngleWord n) (A : (E × ℝ) [×n]→L[ℝ] F)
    (p q : Seminorm ℝ E) {R : ℝ} (hR : 0 ≤ R) {B : ℝ}
    (hbound : ∀ u : Fin n → E × ℝ, w.IsPure u →
      (∀ i, p (u i).1 ≤ 1 ∧ q (u i).1 ≤ R) → ‖A u‖ ≤ B)
    (v : Fin n → E × ℝ)
    (hpure : ∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0)
    (hbox : ∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) :
    ‖A v‖ ≤ B := by
  classical
  let u : Fin n → E × ℝ := fun i => if w.isState i then v i else (0, 1)
  let a : Fin n → ℝ := fun i => if w.isState i then 1 else (v i).2
  have hu : w.IsPure u := by
    constructor
    · intro i hi
      simpa only [u, hi, if_true] using hpure i
    · intro i hi
      simp only [u, hi, Bool.false_eq_true, if_false]
  have hbu (i : Fin n) : p (u i).1 ≤ 1 ∧ q (u i).1 ≤ R := by
    cases hi : w.isState i
    · simpa only [u, hi, Bool.false_eq_true, if_false, map_zero] using
        (show (0 : ℝ) ≤ 1 ∧ 0 ≤ R from ⟨zero_le_one, hR⟩)
    · simpa only [u, hi, if_true] using ⟨(hbox i).1, (hbox i).2.1⟩
  have hvec : (fun i => a i • u i) = v := by
    funext i
    cases hi : w.isState i
    · have hz : (v i).1 = 0 := by
        simpa only [hi, Bool.false_eq_true, if_false] using hpure i
      simp only [a, u, hi, Bool.false_eq_true, if_false, Prod.smul_mk,
        smul_zero, smul_eq_mul, mul_one]
      exact Prod.ext hz.symm rfl
    · simp only [a, u, hi, if_true, one_smul]
  have ha (i : Fin n) : ‖a i‖ ≤ 1 := by
    cases hi : w.isState i
    · simpa only [a, hi, Bool.false_eq_true, if_false] using (hbox i).2.2
    · simp only [a, hi, if_true, norm_one, le_refl]
  have hprod : ‖∏ i, a i‖ ≤ 1 :=
    (Finset.norm_prod_le _ _).trans
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => ha i))
  calc
    ‖A v‖ = ‖∏ i, a i‖ * ‖A u‖ := by
      rw [← hvec, A.map_smul_univ, norm_smul]
    _ ≤ 1 * ‖A u‖ := mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖A u‖ := one_mul _
    _ ≤ B := hbound u hu hbu

/-- A horizon of `s + K` pays for the moving angle while retaining the
original parameter prefix `K`. Only positive inner derivatives enter. -/
theorem n04PositiveGeometry_boundaryMoving_saved_word_bound
    [CompleteSpace F] (K s : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U : Set E} {f : E × ℝ → F} {ψ : E × ℝ → ℝ},
    ∀ JF : SmoothDirections (U ×ˢ (univ : Set ℝ)) f,
    ∀ Jψ : SmoothDirections (U ×ˢ (univ : Set ℝ)) ψ,
    ∀ JO : SmoothDirections (U ×ˢ (univ : Set ℝ)) (fun p => f (p.1, ψ p)),
    ∀ x ∈ U, ∀ θ : ℝ, ∀ p q : Seminorm ℝ E, ∀ R : ℝ, 0 ≤ R →
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift : ℕ,
    N04BoundaryWordBounds JF K (s + K) 1 x (ψ (x, θ))
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryPositiveWordBounds Jψ K (s + K) 1 x θ
      (fun v => p v ≤ 1 ∧ q v ≤ R) M H t shift →
    N04BoundaryWordBounds JO K s 1 x θ (fun v => p v ≤ 1 ∧ q v ≤ R)
      (C * M ^ (2 * (K + s + 1) + 2)) H t (shift + 1) := by
  classical
  choose A hA hAb using (fun n : ℕ =>
    n04PositiveGeometry_movingPoint_unit_saved_word_bound (E := E) (V := ℝ) (Z := F) n)
  let N := K + s + 1
  let C : ℝ := 1 + ∑ j ∈ Finset.range (N + 1), A j
  have hA0 (j : ℕ) : 0 ≤ A j := zero_le_one.trans (hA j)
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => hA0 j)
  have hAC (j : ℕ) (hj : j ≤ N) : A j ≤ C :=
    (Finset.single_le_sum (fun i _ => hA0 i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro U f ψ JF Jψ JO x hx θ p q R hR M H t hM hH hHM ht shift houter hinner
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  intro n w hk ha v hv hp
  have hnN : n ≤ N := by
    have hs := w.arity_sum
    dsimp only [N]
    omega
  by_cases hn : 0 < n
  · have hcost {j : ℕ} (hj : 0 < j) (u : StateAngleWord j) :
        (u.angleArity - 1) + shift * u.stateArity ≤
          u.angleArity + (shift + 1) * u.stateArity - 1 := by
      have hs := u.arity_sum
      rw [Nat.add_mul, one_mul]
      omega
    have hhorizon {j : ℕ} (hjn : j ≤ n) (u : StateAngleWord j) :
        u.angleArity ≤ (s + K) + 1 := by
      have hs := u.arity_sum
      dsimp only [N] at hnN
      omega
    have houter' (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
        (u : StateAngleWord j) (hu : u.stateArity ≤ K)
        (a : Fin j → E × ℝ)
        (hpure : ∀ i, if u.isState i then (a i).2 = 0 else (a i).1 = 0)
        (hbox : ∀ i, p (a i).1 ≤ 1 ∧ q (a i).1 ≤ R ∧ ‖(a i).2‖ ≤ 1) :
        ‖JF.D j (x, ψ (x, θ)) a‖ ≤ M * parameterHeightWeight H u.stateArity *
          t ^ (u.angleArity + (shift + 1) * u.stateArity - 1) := by
      apply boundary_pure_unit_bound u (JF.D j (x, ψ (x, θ))) p q hR ?_ a hpure hbox
      intro b hb hbb
      exact (houter j u hu (hhorizon hjn u) b hb hbb).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (hcost hj u))
          (mul_nonneg hM0 (parameterHeightWeight_nonneg hH _)))
    have hinner' (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
        (u : StateAngleWord j) (hu : u.stateArity ≤ K)
        (a : Fin j → E × ℝ)
        (hpure : ∀ i, if u.isState i then (a i).2 = 0 else (a i).1 = 0)
        (hbox : ∀ i, p (a i).1 ≤ 1 ∧ q (a i).1 ≤ R ∧ ‖(a i).2‖ ≤ 1) :
        ‖Jψ.D j (x, θ) a‖ ≤ M * parameterHeightWeight H u.stateArity *
          t ^ (u.angleArity + (shift + 1) * u.stateArity - 1) := by
      apply boundary_pure_unit_bound u (Jψ.D j (x, θ)) p q hR ?_ a hpure hbox
      intro b hb hbb
      exact (hinner j hj u hu (hhorizon hjn u) b hb hbb).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (hcost hj u))
          (mul_nonneg hM0 (parameterHeightWeight_nonneg hH _)))
    have hpure : ∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0 := by
      intro i
      cases hi : w.isState i
      · simpa only [hi, Bool.false_eq_true, if_false] using
          congrArg (fun z : E × ℝ => z.1) (hv.2 i hi)
      · simpa only [hi, if_true] using hv.1 i hi
    have hbox (i : Fin n) : p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1 := by
      refine ⟨(hp i).1, (hp i).2, ?_⟩
      cases hi : w.isState i
      · rw [hv.2 i hi]
        simp only [norm_one, le_refl]
      · rw [hv.1 i hi, norm_zero]
        exact zero_le_one
    have hb := hAb n (U ×ˢ univ) (U ×ˢ univ) f ψ JF Jψ JO (x, θ)
      ⟨hx, mem_univ _⟩ ⟨hx, mem_univ _⟩ p q R hR M H t hM hH hHM ht
      K (shift + 1) (by omega) houter' hinner' hn w hk v hpure hbox
    have hmat : A n * M ^ (2 * n + 2) ≤ C * M ^ (2 * N + 2) :=
      mul_le_mul (hAC n hnN) (pow_le_pow_right₀ hM (by omega))
        (pow_nonneg hM0 _) hC0
    calc
      _ ≤ A n * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) := hb
      _ ≤ C * M ^ (2 * N + 2) * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmat (parameterHeightWeight_nonneg hH _))
          (pow_nonneg ht0 _)
      _ ≤ C * M ^ (2 * N + 2) * parameterHeightWeight H w.stateArity *
          t ^ ((w.angleArity - 1) + (shift + 1) * w.stateArity) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega))
          (mul_nonneg (mul_nonneg hC0 (pow_nonneg hM0 _))
            (parameterHeightWeight_nonneg hH _))
  · have hn0 : n = 0 := by omega
    subst n
    cases w
    have hv0 : v = Fin.elim0 := by funext i; exact i.elim0
    rw [hv0, JO.zero (x, θ) ⟨hx, mem_univ _⟩]
    have hMM : M ≤ C * M ^ (2 * N + 2) := calc
      _ ≤ M ^ (2 * N + 2) := by
        simpa only [pow_one] using pow_le_pow_right₀ hM (show 1 ≤ 2 * N + 2 by omega)
      _ = 1 * M ^ (2 * N + 2) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (pow_nonneg hM0 _)
    simpa only [StateAngleWord.stateArity, StateAngleWord.angleArity,
      Nat.zero_sub, Nat.mul_zero, Nat.add_zero, parameterHeightWeight, ite_true,
      pow_zero, mul_one] using (houter.value hx).trans hMM

end ContinuousFlexibility.Analysis
