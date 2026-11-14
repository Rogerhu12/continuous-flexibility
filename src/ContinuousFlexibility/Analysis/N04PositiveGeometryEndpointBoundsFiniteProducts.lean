module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaAlgebra
public import ContinuousFlexibility.Analysis.N01cFiniteParameterProducts

/-!
# Finite products with the same root angular reserve

The number of radial factors is finite. Their genuine joint towers are
multiplied before estimating them, and the common word budget survives
each product without charging the reserved angular orders repeatedly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PositiveGeometry_power_product_cost {C M : ℝ} {degree : ℕ}
    (hC : 1 ≤ C) (hM : 1 ≤ M) :
    1 ≤ (1 + C) * M ^ (1 + degree) ∧
      M ≤ (1 + C) * M ^ (1 + degree) ∧
      C * M ^ degree ≤ (1 + C) * M ^ (1 + degree) := by
  have hc : 1 ≤ 1 + C := le_add_of_nonneg_right (zero_le_one.trans hC)
  refine ⟨one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ hM), ?_, ?_⟩
  · simpa only [one_mul, pow_one] using
      mul_le_mul hc (pow_le_pow_right₀ hM (by omega : 1 ≤ 1 + degree))
        (pow_nonneg (zero_le_one.trans hM) 1) (zero_le_one.trans hc)
  · exact mul_le_mul (le_add_of_nonneg_left zero_le_one)
      (pow_le_pow_right₀ hM (by omega : degree ≤ 1 + degree))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hc)

theorem n04PositiveGeometry_boundaryWord_one
    {U : Set E} (J : SmoothDirections (U ×ˢ univ) (fun _ => (1 : ℝ)))
    (K s d : ℕ) (x : E) (hx : x ∈ U) (θ : ℝ) (P : E → Prop)
    {H t : ℝ} (hH : 0 ≤ H) (ht : 0 ≤ t) (shift : ℕ) :
    N04BoundaryWordBounds J K s d x θ P 1 H t shift := by
  intro n w _ _ v _ _
  by_cases hn : n = 0
  · subst n
    cases w
    rw [smoothDirections_D_zero_apply J ⟨hx, mem_univ _⟩]
    simp only [norm_one, StateAngleWord.stateArity, StateAngleWord.angleArity,
      Nat.zero_sub, Nat.mul_zero, Nat.zero_add, parameterHeightWeight,
      ite_true, pow_zero, mul_one, le_refl]
  · rw [smoothDirections_D_constant J (Nat.pos_of_ne_zero hn)
      ⟨hx, mem_univ _⟩ v, norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_one (parameterHeightWeight_nonneg hH _))
      (pow_nonneg ht _)

theorem n04PositiveGeometry_boundaryWord_finiteProduct
    (m N : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
      ∀ {U : Set E}, IsOpen U → ∀ {f : Fin m → E × ℝ → ℝ},
      ∀ J : ∀ i, SmoothDirections (U ×ˢ univ) (f i),
      ∀ Q : SmoothDirections (U ×ˢ univ) (fun y => ∏ i, f i y),
      ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ i, N04BoundaryWordBounds (J i) K s d x θ P M H t shift) →
      N04BoundaryWordBounds Q K s d x θ P (C * M ^ degree) H t shift := by
  induction m with
  | zero =>
      refine ⟨1, le_rfl, 0, ?_⟩
      intro U hU f J Q K s d hN x hx θ P M H t hM hH hHL ht shift hin
      let Q1 : SmoothDirections (U ×ˢ univ) (fun _ => (1 : ℝ)) :=
        Q.congr (fun _ _ => by simp only [Fin.prod_univ_zero])
      have h := n04PositiveGeometry_boundaryWord_one Q1 K s d x hx θ P
        hH (zero_le_one.trans ht) shift
      simpa only [pow_zero, mul_one] using
        h.congr (Q := Q) hx (fun _ _ => by simp only [Fin.prod_univ_zero])
  | succ m ih =>
      obtain ⟨C, hC, degree, htail⟩ := ih
      obtain ⟨Cp, hCp, hmul⟩ := n04PositiveGeometry_boundaryWord_mul (E := E) N L hL
      have hC1 : 1 ≤ 1 + C := le_add_of_nonneg_right (zero_le_one.trans hC)
      refine ⟨Cp * (1 + C) ^ (N + 2),
        one_le_mul_of_one_le_of_one_le hCp (one_le_pow₀ hC1),
        (1 + degree) * (N + 2), ?_⟩
      intro U hU f J Q K s d hN x hx θ P M H t hM hH hHL ht shift hin
      let JT := smoothDirections_finiteProduct (hU.prod isOpen_univ)
        (fun i : Fin m => J i.succ)
      have hb := htail hU (fun i : Fin m => J i.succ) JT
        K s d hN x hx θ P M H t hM hH hHL ht shift (fun i => hin i.succ)
      have hc := n04PositiveGeometry_power_product_cost (degree := degree) hC hM
      have hh := (hin 0).enlarge hH (zero_le_one.trans ht) hc.2.1
      have htb := hb.enlarge hH (zero_le_one.trans ht) hc.2.2
      have hout := hmul (J 0) JT K s d hN x hx θ P
        ((1 + C) * M ^ (1 + degree)) H t hc.1 hH hHL ht shift hh htb
      have heq : EqOn (fun y => f 0 y * ∏ i : Fin m, f i.succ y)
          (fun y => ∏ i : Fin (m + 1), f i y) (U ×ˢ univ) := by
        intro y _
        exact (Fin.prod_univ_succ (fun i => f i y)).symm
      have hresult := hout.congr (Q := Q) hx heq
      simpa only [mul_pow, ← pow_mul, mul_assoc] using hresult

end ContinuousFlexibility.Analysis
