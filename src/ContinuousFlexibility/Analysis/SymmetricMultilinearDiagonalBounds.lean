import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform diagonal bounds for symmetric multilinear forms

At fixed arity, the diagonal on a unit ball determines a symmetric
multilinear form. On the finite-dimensional space of forms on `ℝⁿ`,
this injective linear map has a bounded inverse on its image. Pulling
an arbitrary algebraic form back along a finite family of directions
therefore gives a polarization bound whose constant depends only on
the arity. No norm, completeness, or continuity assumption on the
original parameter space is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped BigOperators

private abbrev DiagonalParameterSpace (n : ℕ) := Fin n → ℝ

private def symmetricParameterForms (n : ℕ) :
    Submodule ℝ ((DiagonalParameterSpace n) [×n]→L[ℝ] ℝ) where
  carrier := {A | ∀ v (σ : Equiv.Perm (Fin n)), A (v ∘ σ) = A v}
  zero_mem' := by intro v σ; simp
  add_mem' := by
    intro A B hA hB v σ
    simp only [ContinuousMultilinearMap.add_apply, hA v σ, hB v σ]
  smul_mem' := by
    intro c A hA v σ
    simp only [ContinuousMultilinearMap.smul_apply, hA v σ]

private instance parameterForms_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ ((DiagonalParameterSpace n) [×n]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear :
      ((DiagonalParameterSpace n) [×n]→L[ℝ] ℝ) →ₗ[ℝ]
        MultilinearMap ℝ (fun _ : Fin n => DiagonalParameterSpace n) ℝ)
    ContinuousMultilinearMap.toMultilinearMap_injective

private abbrev DiagonalUnitBall (n : ℕ) :=
  {x : DiagonalParameterSpace n // ‖x‖ ≤ 1}

private def parameterDiagonalMap (n : ℕ) :
    symmetricParameterForms n →ₗ[ℝ] BoundedContinuousFunction (DiagonalUnitBall n) ℝ where
  toFun A := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => A.val (fun _ => x.val))
    (A.val.cont.comp (continuous_pi (fun _ : Fin n => continuous_subtype_val)))
    ‖A.val‖ (fun x => by
      apply (A.val.le_opNorm (fun _ => x.val)).trans
      have hprod : (∏ _i : Fin n, ‖x.val‖) ≤ 1 := by
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg x.val) (fun _ _ => x.property)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (norm_nonneg A.val))
  map_add' A B := by
    ext x
    exact ContinuousMultilinearMap.add_apply A.val B.val (fun _ => x.val)
  map_smul' c A := by
    ext x
    exact smul_apply A.val c (fun _ : Fin n => x.val)

private theorem parameterDiagonalMap_apply (n : ℕ) (A : symmetricParameterForms n)
    (x : DiagonalUnitBall n) : parameterDiagonalMap n A x = A.val (fun _ => x.val) := rfl

private theorem parameterDiagonalMap_injective (n : ℕ) :
    Function.Injective (parameterDiagonalMap n) := by
  classical
  have hzero : ∀ A : symmetricParameterForms n,
      parameterDiagonalMap n A = 0 → A = 0 := by
    intro A hA
    have hunit (x : DiagonalParameterSpace n) (hx : ‖x‖ ≤ 1) :
        A.val (fun _ => x) = 0 := by
      exact congrArg (fun g : BoundedContinuousFunction (DiagonalUnitBall n) ℝ => g ⟨x, hx⟩) hA
    have hdiag (x : DiagonalParameterSpace n) : A.val (fun _ => x) = 0 := by
      let c : ℝ := (1 + ‖x‖)⁻¹
      have hcpos : 0 < c := inv_pos.mpr (by positivity)
      have hc : c * (1 + ‖x‖) = 1 := inv_mul_cancel₀ (by positivity)
      have hnorm : ‖c • x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
        nlinarith only [hc, hcpos]
      have hscale : A.val (fun _ => c • x) = c ^ n * A.val (fun _ => x) := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
          A.val.map_smul_univ (fun _ => c) (fun _ => x)
      have hz : c ^ n * A.val (fun _ => x) = 0 := hscale.symm.trans (hunit (c • x) hnorm)
      exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero n hcpos.ne')
    apply Subtype.ext
    ext v
    have h := A.val.iteratedFDeriv_comp_diagonal (0 : DiagonalParameterSpace n) v
    have hf : (fun x : DiagonalParameterSpace n => A.val (fun _ => x)) =
        fun _ => (0 : ℝ) := funext hdiag
    rw [hf] at h
    have hsym (σ : Equiv.Perm (Fin n)) : A.val (fun i => v (σ i)) = A.val v :=
      A.property v σ
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply,
      ContinuousMultilinearMap.zero_apply, hsym, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at h
    have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := Equiv.Perm (Fin n)))
    exact (mul_eq_zero.mp h.symm).resolve_left hcard
  intro A B hAB
  exact sub_eq_zero.mp (hzero (A - B) (by rw [map_sub, hAB, sub_self]))

/-- The diagonal unit-ball estimate controls every unit tuple in the
fixed finite-dimensional model, with a constant chosen before the form. -/
theorem exists_symmetric_diagonal_unit_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (A : (Fin n → ℝ) [×n]→L[ℝ] ℝ),
        (∀ v (σ : Equiv.Perm (Fin n)), A (v ∘ σ) = A v) →
      ∀ C : ℝ, 0 ≤ C → (∀ x, ‖x‖ ≤ 1 → |A (fun _ => x)| ≤ C) →
      ∀ v : Fin n → (Fin n → ℝ), (∀ i, ‖v i‖ ≤ 1) → |A v| ≤ K * C := by
  obtain ⟨K, hK, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (𝕜 := ℝ)
      (E := symmetricParameterForms n)
      (F := BoundedContinuousFunction (DiagonalUnitBall n) ℝ)
      (parameterDiagonalMap n)).mp
      (parameterDiagonalMap_injective n)
  refine ⟨K, K.coe_nonneg, fun A hsym C hC hdiag v hv => ?_⟩
  let B : symmetricParameterForms n := ⟨A, hsym⟩
  have hnorm : ‖parameterDiagonalMap n B‖ ≤ C :=
    (BoundedContinuousFunction.norm_le hC).mpr (fun x => by
      simpa only [parameterDiagonalMap_apply, Real.norm_eq_abs] using hdiag x.val x.property)
  have hbound : ‖A‖ ≤ (K : ℝ) * C := by
    exact (ZeroHomClass.bound_of_antilipschitz (parameterDiagonalMap n) hanti B).trans
      (mul_le_mul_of_nonneg_left hnorm K.coe_nonneg)
  have hprod : (∏ i : Fin n, ‖v i‖) ≤ 1 := by
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg (v i)) (fun i _ => hv i)
  rw [← Real.norm_eq_abs]
  exact (A.le_opNorm v).trans ((mul_le_mul_of_nonneg_left hprod (norm_nonneg A)).trans
    (by simpa only [mul_one] using hbound))

private def finiteDirectionSum {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (v : Fin n → E) : (Fin n → ℝ) →ₗ[ℝ] E where
  toFun t := ∑ i, t i • v i
  map_add' s t := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c t := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

private theorem finiteDirectionSum_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (v : Fin n → E) (t : Fin n → ℝ) :
    finiteDirectionSum v t = ∑ i, t i • v i := rfl

private def finiteDirectionPullback {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) ℝ) (v : Fin n → E) :
    (Fin n → ℝ) [×n]→L[ℝ] ℝ :=
  { A.compLinearMap (fun _ => finiteDirectionSum v) with
    cont := by
      classical
      have heq : (fun t : Fin n → (Fin n → ℝ) =>
          A.compLinearMap (fun _ => finiteDirectionSum v) t) =
          fun t => ∑ s : Fin n → Fin n, (∏ i, t i (s i)) * A (fun i => v (s i)) := by
        funext t
        rw [MultilinearMap.compLinearMap_apply]
        simp only [finiteDirectionSum_apply]
        rw [A.map_sum]
        apply Finset.sum_congr rfl
        intro s hs
        simpa only [smul_eq_mul] using A.map_smul_univ (fun i => t i (s i))
          (fun i => v (s i))
      change Continuous (fun t : Fin n → (Fin n → ℝ) =>
        A.compLinearMap (fun _ => finiteDirectionSum v) t)
      rw [heq]
      fun_prop }

private theorem finiteDirectionPullback_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (A : MultilinearMap ℝ (fun _ : Fin n => E) ℝ) (v : Fin n → E)
    (t : Fin n → (Fin n → ℝ)) :
    finiteDirectionPullback A v t = A (fun i => ∑ j, t i j • v j) := rfl

private theorem seminorm_finite_sum_le {E I : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (s : Finset I) (v : I → E) :
    p (∑ i ∈ s, v i) ≤ ∑ i ∈ s, p (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero, le_refl]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

/-- A same-direction affine bound controls arbitrary parameter directions.
The constant is chosen before the parameter space, the two seminorms,
the form, the base point, and its diagonal bound. -/
theorem exists_symmetric_multilinear_diagonal_affine_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (E : Type*) [AddCommGroup E] [Module ℝ E]
        (p q : Seminorm ℝ E) (A : MultilinearMap ℝ (fun _ : Fin n => E) ℝ),
      (∀ v (σ : Equiv.Perm (Fin n)), A (v ∘ σ) = A v) →
      ∀ (x : E) (C : ℝ), 0 ≤ C →
        (∀ w, p w ≤ 1 → |A (fun _ => w)| ≤ C * (1 + q x + q w)) →
      ∀ v : Fin n → E, (∀ i, p (v i) ≤ 1) →
        |A v| ≤ K * C * (1 + q x + ∑ i, q (v i)) := by
  classical
  obtain ⟨K, hK, hbound⟩ := exists_symmetric_diagonal_unit_bound n
  let d : ℝ := (n : ℝ) + 1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hd1 : 1 ≤ d := by
    dsimp only [d]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  refine ⟨d ^ n * K, mul_nonneg (pow_nonneg hd.le _) hK, ?_⟩
  intro E _ _ p q A hsym x C hC hdiag v hv
  let c : ℝ := d⁻¹
  have hc : 0 < c := inv_pos.mpr hd
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ hd1
  have hcd : c * d = 1 := inv_mul_cancel₀ hd.ne'
  let B := finiteDirectionPullback A (fun i => c • v i)
  let H : ℝ := 1 + q x + ∑ i, q (v i)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hBsym (t : Fin n → (Fin n → ℝ)) (σ : Equiv.Perm (Fin n)) :
      B (t ∘ σ) = B t := by
    exact hsym (fun i => ∑ j, t i j • (c • v j)) σ
  have hBdiag (t : Fin n → ℝ) (ht : ‖t‖ ≤ 1) : |B (fun _ => t)| ≤ C * H := by
    let w : E := ∑ i, t i • (c • v i)
    have htcoord (i : Fin n) : |t i| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm t i).trans ht
    have hpw : p w ≤ 1 := by
      calc
        p w ≤ ∑ i, p (t i • (c • v i)) := seminorm_finite_sum_le p _ _
        _ = ∑ i, |t i| * (c * p (v i)) := by
          simp only [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ ∑ _i : Fin n, c := Finset.sum_le_sum (fun i _ => by
          exact (mul_le_mul (htcoord i) (mul_le_mul_of_nonneg_left (hv i) hc.le)
            (mul_nonneg hc.le (apply_nonneg p (v i))) zero_le_one).trans_eq (by ring))
        _ = (n : ℝ) * c := by simp
        _ ≤ 1 := by dsimp only [d] at hcd; nlinarith only [hcd, hc]
    have hqw : q w ≤ ∑ i, q (v i) := by
      calc
        q w ≤ ∑ i, q (t i • (c • v i)) := seminorm_finite_sum_le q _ _
        _ = ∑ i, |t i| * (c * q (v i)) := by
          simp only [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ ∑ i, q (v i) := Finset.sum_le_sum (fun i _ => by
          exact (mul_le_mul (htcoord i)
            (mul_le_mul_of_nonneg_right hc1 (apply_nonneg q (v i)))
            (mul_nonneg hc.le (apply_nonneg q (v i))) zero_le_one).trans_eq (by ring))
    exact (hdiag w hpw).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hqw) hC)
  let e : Fin n → (Fin n → ℝ) := fun i => Pi.single i 1
  have he (i : Fin n) : ‖e i‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    by_cases hij : j = i
    · subst j; simp [e]
    · simp [e, Pi.single_apply, hij, Ne.symm hij]
  have hBe := hbound B hBsym (C * H) (mul_nonneg hC hH) hBdiag e he
  have heval : B e = c ^ n * A v := by
    rw [finiteDirectionPullback_apply]
    have hsum (i : Fin n) : (∑ j, e i j • (c • v j)) = c • v i := by
      simp [e, Pi.single_apply, eq_comm]
    simp only [hsum]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      A.map_smul_univ (fun _ => c) v
  have hscale : d ^ n * B e = A v := by
    rw [heval, ← mul_assoc, ← mul_pow]
    have hdc : d * c = 1 := by simpa only [mul_comm] using hcd
    rw [hdc, one_pow, one_mul]
  calc
    |A v| = d ^ n * |B e| := by rw [← hscale, abs_mul, abs_of_nonneg (pow_nonneg hd.le _)]
    _ ≤ d ^ n * (K * (C * H)) := mul_le_mul_of_nonneg_left hBe (pow_nonneg hd.le _)
    _ = (d ^ n * K) * C * (1 + q x + ∑ i, q (v i)) := by dsimp only [H]; ring

end ContinuousFlexibility.Analysis
