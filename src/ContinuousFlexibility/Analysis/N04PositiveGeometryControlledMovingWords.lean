import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledMovingAffine
import ContinuousFlexibility.Analysis.N01cFiniteAffineMixedJets
import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Returning the finite-slice estimate to the original unit directions

The slice is the average of the prescribed state directions. Its unit
ball lies in both original seminorm boxes. The coordinate vectors that
recover the prescribed directions cost only `(n+1)^n`, independently of
the low state order and the common high radius.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_norm_le_prod_of_unit
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (A : X [×n]→L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hunit : ∀ v : Fin n → X, (∀ i, ‖v i‖ ≤ 1) → ‖A v‖ ≤ C)
    (v : Fin n → X) : ‖A v‖ ≤ C * ∏ i, ‖v i‖ := by
  have h := multilinear_bound_of_unitBall A (normSeminorm ℝ F)
    (normSeminorm ℝ X) 0 hC (a := 1) (fun u hu => by
      simpa [coe_normSeminorm] using hunit u (fun i => (hu i).le)) v
  simpa [coe_normSeminorm, multilinearTameSize] using h

variable {E V Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

private theorem moving_seminorm_sum_le {ι : Type*}
    (p : Seminorm ℝ E) (s : Finset ι) (u : ι → E) :
    p (∑ i ∈ s, u i) ≤ ∑ i ∈ s, p (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero, le_refl]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

/-- The same averaging slice preserves each of the original seminorm
boxes, including a common high box of arbitrary nonnegative radius. -/
theorem n04PositiveGeometry_finiteDirectionAverage_bound
    {n : ℕ} (p : Seminorm ℝ E) {R : ℝ} (hR : 0 ≤ R)
    (v : Fin n → E) (hv : ∀ i, p (v i) ≤ R)
    (a : Fin n → ℝ) (ha : ‖a‖ ≤ 1) :
    p ((((n + 1 : ℕ) : ℝ)⁻¹ • finiteDirectionMap v) a) ≤ R := by
  have hd : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hterm (i : Fin n) : p (a i • v i) ≤ R := by
    rw [map_smul_eq_mul]
    exact (mul_le_mul ((pi_norm_le_iff_of_nonneg zero_le_one).mp ha i)
      (hv i) (apply_nonneg _ _) zero_le_one).trans_eq (one_mul _)
  have hsum : p (finiteDirectionMap v a) ≤ ((n + 1 : ℕ) : ℝ) * R := by
    rw [finiteDirectionMap_apply]
    calc
      _ ≤ ∑ i : Fin n, p (a i • v i) := moving_seminorm_sum_le p _ _
      _ ≤ ∑ _i : Fin n, R := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (n : ℝ) * R := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((n + 1 : ℕ) : ℝ) * R :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hR
  change p (((n + 1 : ℕ) : ℝ)⁻¹ • finiteDirectionMap v a) ≤ R
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hd.le)).trans_eq (by
    rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul])

/-- The original joint tower obeys the same moving-point budget on the
unit low and common high boxes. No norm is imposed on the state space. -/
theorem n04PositiveGeometry_movingPoint_unit_word_bound
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
          M * parameterHeightWeight H w.stateArity * t ^ (w.angleArity + C * w.stateArity)) →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ∀ v : Fin j → E × V,
        (∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0) →
        (∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) →
        ‖JG.D j x v‖ ≤
          M * parameterHeightWeight H w.stateArity * t ^ (w.angleArity + C * w.stateArity - 1)) →
      0 < n → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → E × V,
      (∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0) →
      (∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) →
        ‖JO.D n x v‖ ≤ A * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + C * w.stateArity) := by
  classical
  obtain ⟨A, hA, hbound⟩ := n04PositiveGeometry_movingPoint_affine_bound
    (E := E) (P := Fin n → ℝ) (V := V) (Z := Z) n
  let d : ℝ := ((n + 1 : ℕ) : ℝ)
  have hd : 1 ≤ d := by dsimp only [d]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hdpos : 0 < d := zero_lt_one.trans_le hd
  refine ⟨A * d ^ n, one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hd), ?_⟩
  intro U W f g JF JG JO x hx hfx p q R hR M H t hM hH hHM ht K C hC
    houter hinner hn w hw v hpure hv
  let L : (Fin n → ℝ) →L[ℝ] E := d⁻¹ • finiteDirectionMap (fun i => (v i).1)
  have hpoint : n04PositiveGeometry_fiberSlice x.1 L (0, x.2) = x := by
    rw [n04PositiveGeometry_fiberSlice_apply, map_zero, add_zero]
  have hgood {j : ℕ} (u : StateAngleWord j) (a : Fin j → (Fin n → ℝ) × V)
      (ha : ∀ i, ‖a i‖ ≤ 1) :
      (∀ i, if u.isState i then
        (n04PositiveGeometry_fiberSliceLinear L (n04PositiveGeometry_slotProjection (u.isState i) (a i))).2 = 0
        else (n04PositiveGeometry_fiberSliceLinear L
          (n04PositiveGeometry_slotProjection (u.isState i) (a i))).1 = 0) ∧
      (∀ i, p (n04PositiveGeometry_fiberSliceLinear L
            (n04PositiveGeometry_slotProjection (u.isState i) (a i))).1 ≤ 1 ∧
        q (n04PositiveGeometry_fiberSliceLinear L
            (n04PositiveGeometry_slotProjection (u.isState i) (a i))).1 ≤ R ∧
        ‖(n04PositiveGeometry_fiberSliceLinear L
            (n04PositiveGeometry_slotProjection (u.isState i) (a i))).2‖ ≤ 1) := by
    constructor
    · intro i
      cases hi : u.isState i <;>
        simp only [n04PositiveGeometry_slotProjection_apply, hi, Bool.false_eq_true,
          if_false, if_true, n04PositiveGeometry_fiberSliceLinear_apply, map_zero]
    · intro i
      have hfst : ‖(a i).1‖ ≤ 1 := (norm_fst_le (a i)).trans (ha i)
      cases hi : u.isState i
      · simp only [n04PositiveGeometry_slotProjection_apply, hi, Bool.false_eq_true,
          if_false, n04PositiveGeometry_fiberSliceLinear_apply, map_zero]
        exact ⟨zero_le_one, hR, (norm_snd_le (a i)).trans (ha i)⟩
      · simp only [n04PositiveGeometry_slotProjection_apply, hi, if_true,
          n04PositiveGeometry_fiberSliceLinear_apply, norm_zero]
        exact ⟨n04PositiveGeometry_finiteDirectionAverage_bound p zero_le_one
            (fun i => (v i).1) (fun i => (hv i).1) _ hfst,
          n04PositiveGeometry_finiteDirectionAverage_bound q hR
            (fun i => (v i).1) (fun i => (hv i).2.1) _ hfst, zero_le_one⟩
  have houter' (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (u : StateAngleWord j) (hu : u.stateArity ≤ K)
      (a : Fin j → (Fin n → ℝ) × V) :
      ‖JF.D j ((n04PositiveGeometry_fiberSlice x.1 L (0, x.2)).1,
          g (n04PositiveGeometry_fiberSlice x.1 L (0, x.2)))
        (fun i => n04PositiveGeometry_fiberSliceLinear L
          (n04PositiveGeometry_slotProjection (u.isState i) (a i)))‖ ≤
        M * parameterHeightWeight H u.stateArity * t ^ (u.angleArity + C * u.stateArity) *
          ∏ i, ‖a i‖ := by
    rw [hpoint]
    let B := (JF.D j (x.1, g x)).compContinuousLinearMap
      (fun i => (n04PositiveGeometry_fiberSliceLinear L).comp
        (n04PositiveGeometry_slotProjection (u.isState i)))
    apply n04PositiveGeometry_norm_le_prod_of_unit B
      (mul_nonneg (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
        (pow_nonneg (zero_le_one.trans ht) _))
    intro b hb
    exact houter j hj hjn u hu _ (hgood u b hb).1 (hgood u b hb).2
  have hinner' (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (u : StateAngleWord j) (hu : u.stateArity ≤ K)
      (a : Fin j → (Fin n → ℝ) × V) :
      ‖JG.D j (n04PositiveGeometry_fiberSlice x.1 L (0, x.2))
        (fun i => n04PositiveGeometry_fiberSliceLinear L
          (n04PositiveGeometry_slotProjection (u.isState i) (a i)))‖ ≤
        M * parameterHeightWeight H u.stateArity * t ^ (u.angleArity + C * u.stateArity - 1) *
          ∏ i, ‖a i‖ := by
    rw [hpoint]
    let B := (JG.D j x).compContinuousLinearMap
      (fun i => (n04PositiveGeometry_fiberSliceLinear L).comp
        (n04PositiveGeometry_slotProjection (u.isState i)))
    apply n04PositiveGeometry_norm_le_prod_of_unit B
      (mul_nonneg (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
        (pow_nonneg (zero_le_one.trans ht) _))
    intro b hb
    exact hinner j hj hjn u hu _ (hgood u b hb).1 (hgood u b hb).2
  let e : Fin n → (Fin n → ℝ) × V := fun i => (d • Pi.single i 1, (v i).2)
  have hLe (i : Fin n) : L (e i).1 = (v i).1 := by
    change d⁻¹ • finiteDirectionMap (fun i => (v i).1) (d • Pi.single i 1) = _
    rw [map_smul, finiteDirectionMap_single, one_smul, smul_smul,
      inv_mul_cancel₀ hdpos.ne', one_smul]
  have hdir : (fun i => n04PositiveGeometry_fiberSliceLinear L
      (n04PositiveGeometry_slotProjection (w.isState i) (e i))) = v := by
    funext i
    have hi := hpure i
    cases hb : w.isState i <;>
      simp only [n04PositiveGeometry_slotProjection_apply, hb, Bool.false_eq_true,
        if_false, if_true, n04PositiveGeometry_fiberSliceLinear_apply, map_zero] at hi ⊢
    · exact Prod.ext hi.symm rfl
    · exact Prod.ext (hLe i) hi.symm
  have he (i : Fin n) : ‖e i‖ ≤ d := by
    have hδ : ‖(Pi.single i 1 : Fin n → ℝ)‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro j
      by_cases hij : i = j <;> simp [Pi.single_apply, hij, eq_comm]
    change max ‖d • (Pi.single i 1 : Fin n → ℝ)‖ ‖(v i).2‖ ≤ d
    refine max_le ?_ ((hv i).2.2.trans hd)
    rw [norm_smul, Real.norm_of_nonneg hdpos.le]
    exact (mul_le_mul_of_nonneg_left hδ hdpos.le).trans_eq (mul_one _)
  have hbnd := hbound U W f g JF JG JO x.1 L (0, x.2)
    (by rw [hpoint]; exact hx) (by rw [hpoint]; exact hfx)
    M H t hM hH hHM ht K C hC houter' hinner' hn w hw e
  rw [hpoint, hdir] at hbnd
  have hprod : (∏ i, ‖e i‖) ≤ d ^ n :=
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => he i)).trans_eq
      (by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  calc
    _ ≤ A * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + C * w.stateArity) * ∏ i, ‖e i‖ := hbnd
    _ ≤ A * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + C * w.stateArity) * d ^ n :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg
        (mul_nonneg (mul_nonneg (zero_le_one.trans hA) (pow_nonneg (zero_le_one.trans hM) _))
          (parameterHeightWeight_nonneg hH _)) (pow_nonneg (zero_le_one.trans ht) _))
    _ = _ := by ring

end ContinuousFlexibility.Analysis
