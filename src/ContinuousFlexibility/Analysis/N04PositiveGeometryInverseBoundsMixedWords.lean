import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedAffine
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledMovingWords

/-!
# Actual inverse words on the original seminorm boxes

An averaged finite slice preserves both original state boxes. Recovering
the prescribed directions costs only a constant depending on their
number. The inverse equation and the true spatial inverse differential
are the sole inverse inputs; every quantitative jet premise is forward.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E V : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V]

/-- The actual inverse tower satisfies the saved word bound on the
original low and high seminorm boxes. Only positive forward jets in the
requested parameter prefix are used, and no zeroth value is bounded. -/
theorem n04PositiveGeometry_mixedInverse_unit_word_bound
    (n : ℕ) : ∃ A : ℝ, 1 ≤ A ∧ ∃ degree : ℕ,
    ∀ (U W : Set (E × V)) (f g : E × V → V)
      (JF : SmoothDirections W f) (JG : SmoothDirections U g)
      (x : E × V), x ∈ U → (x.1, g x) ∈ W →
      (∀ y ∈ U, f (y.1, g y) = y.2) →
    ∀ (p q : Seminorm ℝ E) (R : ℝ), 0 ≤ R →
    ∀ (M H t : ℝ), 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t →
    ∀ (K C : ℕ), 1 ≤ C → ∀ B : V →L[ℝ] V,
      (∀ v : V, B (JF.D 1 (x.1, g x) (fun _ => (0, v))) = v) → ‖B‖ ≤ M →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ∀ v : Fin j → E × V,
        (∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0) →
        (∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) →
        ‖JF.D j (x.1, g x) v‖ ≤ M * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + C * w.stateArity - 1)) →
      0 < n → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → E × V,
      (∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0) →
      (∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) →
        ‖JG.D n x v‖ ≤ A * M ^ degree * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + C * w.stateArity - 1) := by
  classical
  obtain ⟨A, hA, degree, hbound⟩ := n04PositiveGeometry_mixedInverse_affine_bound
    (E := E) (P := Fin n → ℝ) (V := V) n
  let d : ℝ := ((n + 1 : ℕ) : ℝ)
  have hd : 1 ≤ d := by
    dsimp only [d]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hdpos : 0 < d := zero_lt_one.trans_le hd
  refine ⟨A * d ^ n, one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hd), degree, ?_⟩
  intro U W f g JF JG x hx hfx hfg p q R hR M H t hM hH hHM ht K C hC B hB hBM
    hforward hn w hw v hpure hv
  let L : (Fin n → ℝ) →L[ℝ] E := d⁻¹ • finiteDirectionMap (fun i => (v i).1)
  have hpoint : n04PositiveGeometry_fiberSlice x.1 L (0, x.2) = x := by
    rw [n04PositiveGeometry_fiberSlice_apply, map_zero, add_zero]
  have hgood {j : ℕ} (u : StateAngleWord j) (a : Fin j → (Fin n → ℝ) × V)
      (ha : ∀ i, ‖a i‖ ≤ 1) :
      (∀ i, if u.isState i then
        (n04PositiveGeometry_fiberSliceLinear L
          (n04PositiveGeometry_slotProjection (u.isState i) (a i))).2 = 0
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
  have hforward' (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (u : StateAngleWord j) (hu : u.stateArity ≤ K)
      (a : Fin j → (Fin n → ℝ) × V) :
      ‖JF.D j ((n04PositiveGeometry_fiberSlice x.1 L (0, x.2)).1,
          g (n04PositiveGeometry_fiberSlice x.1 L (0, x.2)))
        (fun i => n04PositiveGeometry_fiberSliceLinear L
          (n04PositiveGeometry_slotProjection (u.isState i) (a i)))‖ ≤
        M * parameterHeightWeight H u.stateArity *
          t ^ (u.angleArity + C * u.stateArity - 1) * ∏ i, ‖a i‖ := by
    rw [hpoint]
    let T := (JF.D j (x.1, g x)).compContinuousLinearMap
      (fun i => (n04PositiveGeometry_fiberSliceLinear L).comp
        (n04PositiveGeometry_slotProjection (u.isState i)))
    apply n04PositiveGeometry_norm_le_prod_of_unit T
      (mul_nonneg (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
        (pow_nonneg (zero_le_one.trans ht) _))
    intro b hb
    exact hforward j hj hjn u hu _ (hgood u b hb).1 (hgood u b hb).2
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
  have hbnd := hbound U W f g JF JG x.1 L (0, x.2)
    (by rw [hpoint]; exact hx) (by rw [hpoint]; exact hfx) hfg
    M H t hM hH hHM ht K C hC B (fun a => by rw [hpoint]; exact hB a)
    hBM hforward' hn w hw e
  rw [hpoint, hdir] at hbnd
  have hprod : (∏ i, ‖e i‖) ≤ d ^ n :=
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => he i)).trans_eq
      (by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  calc
    _ ≤ A * M ^ degree * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + C * w.stateArity - 1) * ∏ i, ‖e i‖ := hbnd
    _ ≤ A * M ^ degree * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + C * w.stateArity - 1) * d ^ n :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg
        (mul_nonneg (mul_nonneg (zero_le_one.trans hA) (pow_nonneg (zero_le_one.trans hM) _))
          (parameterHeightWeight_nonneg hH _)) (pow_nonneg (zero_le_one.trans ht) _))
    _ = _ := by ring

end ContinuousFlexibility.Analysis
