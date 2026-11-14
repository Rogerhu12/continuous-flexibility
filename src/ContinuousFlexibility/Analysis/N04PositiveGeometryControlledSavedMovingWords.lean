module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledMovingWords
public import ContinuousFlexibility.Analysis.N01cParameterCalculus

/-!
# Moving-point composition with a saved ordinary order

Multiplying the actual outer function by the fixed positive scale turns
its saved positive-order bound into the existing unsaved bound. The same
linear operation on the actual output tower is cancelled at the end.
Neither input is required to have a bounded zeroth value.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem moving_saved_rescale (t a : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    t * (a * t ^ (d - 1)) = a * t ^ d := by
  have he : d - 1 + 1 = d := Nat.sub_add_cancel hd
  calc
    _ = a * (t ^ (d - 1) * t) := by ring
    _ = _ := by rw [← pow_succ, he]

variable {E V Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- Positive-order saved bounds for both actual inputs give the same
saved bound for their actual moving-point composition. -/
theorem n04PositiveGeometry_movingPoint_unit_saved_word_bound
    (n : ℕ) : ∃ A : ℝ, 1 ≤ A ∧
    ∀ (U W : Set (E × V)) (f : E × V → Z) (g : E × V → V)
      (JF : SmoothDirections W f) (JG : SmoothDirections U g)
      (JO : SmoothDirections U (fun y => f (y.1, g y)))
      (x : E × V), x ∈ U → (x.1, g x) ∈ W →
    ∀ (p q : Seminorm ℝ E) (R : ℝ), 0 ≤ R →
    ∀ (M H t : ℝ), 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t →
    ∀ (K C : ℕ), 1 ≤ C →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ∀ v : Fin j → E × V,
        (∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0) →
        (∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) →
        ‖JF.D j (x.1, g x) v‖ ≤
          M * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + C * w.stateArity - 1)) →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ∀ v : Fin j → E × V,
        (∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0) →
        (∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) →
        ‖JG.D j x v‖ ≤
          M * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + C * w.stateArity - 1)) →
      0 < n → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → E × V,
      (∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0) →
      (∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) →
        ‖JO.D n x v‖ ≤ A * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + C * w.stateArity - 1) := by
  obtain ⟨A, hA, hbound⟩ := n04PositiveGeometry_movingPoint_unit_word_bound
    (E := E) (V := V) (Z := Z) n
  refine ⟨A, hA, ?_⟩
  intro U W f g JF JG JO x hx hfx p q R hR M H t hM hH hHM ht K C hC
    houter hinner hn w hw v hpure hv
  let L : Z →L[ℝ] Z := t • ContinuousLinearMap.id ℝ Z
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have horder {j : ℕ} (hj : 0 < j) (u : StateAngleWord j) :
      1 ≤ u.angleArity + C * u.stateArity := by
    have hs := u.arity_sum
    have hm : u.stateArity ≤ C * u.stateArity := by
      simpa only [one_mul] using Nat.mul_le_mul_right u.stateArity hC
    omega
  have houter' (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (u : StateAngleWord j) (hu : u.stateArity ≤ K)
      (a : Fin j → E × V)
      (ha : ∀ i, if u.isState i then (a i).2 = 0 else (a i).1 = 0)
      (hbox : ∀ i, p (a i).1 ≤ 1 ∧ q (a i).1 ≤ R ∧ ‖(a i).2‖ ≤ 1) :
      ‖(smoothDirections_postcompCLM JF L).D j (x.1, g x) a‖ ≤
        M * parameterHeightWeight H u.stateArity *
          t ^ (u.angleArity + C * u.stateArity) := by
    rw [smoothDirections_postcompCLM_D_apply]
    change ‖t • JF.D j (x.1, g x) a‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_left (houter j hj hjn u hu a ha hbox) ht0).trans_eq
      (moving_saved_rescale t (M * parameterHeightWeight H u.stateArity) (horder hj u))
  have hb := hbound U W (L ∘ f) g (smoothDirections_postcompCLM JF L) JG
    (smoothDirections_postcompCLM JO L) x hx hfx p q R hR M H t hM hH hHM ht
    K C hC houter' hinner hn w hw v hpure hv
  apply (mul_le_mul_iff_right₀ (zero_lt_one.trans_le ht)).mp
  calc
    t * ‖JO.D n x v‖ = ‖(smoothDirections_postcompCLM JO L).D n x v‖ := by
      rw [smoothDirections_postcompCLM_D_apply]
      change t * ‖JO.D n x v‖ = ‖t • JO.D n x v‖
      rw [norm_smul, Real.norm_of_nonneg ht0]
    _ ≤ A * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + C * w.stateArity) := hb
    _ = t * (A * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + C * w.stateArity - 1)) :=
      (moving_saved_rescale t
        (A * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity) (horder hn w)).symm

end ContinuousFlexibility.Analysis
