module

public import ContinuousFlexibility.Analysis.N04FlowPolynomialBounds

/-!
# Exact spatial powers for the actual regularized flow

The existing flow-jet polynomial records field order minus one as its
weight. Evaluating this polynomial at geometrically weighted field jets
therefore preserves precisely that weight. Only the finite prefix being
estimated enters the numerical cost; higher raw bounds merely provide a
bound for the smooth field outside the prefix.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem list_member_le_sum (ks : List ℕ) {k : ℕ} (hk : k ∈ ks) :
    k ≤ ks.sum := by
  induction ks with
  | nil => cases hk
  | cons j ks ih =>
    rcases List.mem_cons.mp hk with h | h
    · subst k
      simp only [List.sum_cons]
      omega
    · have hb := ih h
      simp only [List.sum_cons]
      omega

private theorem weighted_list_product_le
    (ks : List ℕ) (X : ℕ → ℝ) {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (hX : ∀ k, 0 ≤ X k) (hbound : ∀ k ∈ ks, X k ≤ A * ρ ^ k) :
    (ks.map X).prod ≤ A ^ ks.length * ρ ^ ks.sum := by
  induction ks with
  | nil => simp only [List.map_nil, List.prod_nil, List.length_nil,
      List.sum_nil, pow_zero, one_mul, le_refl]
  | cons k ks ih =>
    have hp : 0 ≤ (ks.map X).prod := List.prod_nonneg (by
      intro y hy
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
      exact hX j)
    have ht := ih (fun j hj => hbound j (List.mem_cons_of_mem k hj))
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons]
    calc
      _ ≤ (A * ρ ^ k) * (A ^ ks.length * ρ ^ ks.sum) :=
        mul_le_mul (hbound k List.mem_cons_self) ht hp (mul_nonneg hA (pow_nonneg hρ k))
      _ = _ := by rw [pow_succ, pow_add]; ring

/-- A nonnegative polynomial of weighted degree n costs only ρ^n.
Its ordinary polynomial degree may grow with the chosen finite prefix. -/
theorem n04NegativeGeometry_flowPolynomial_weighted_prefix
    (P : FlowJetPolynomial) (n : ℕ) (hP : FlowJetPolynomialDegreeLE P n) :
    ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧ ∀ {A ρ : ℝ}, 1 ≤ A → 1 ≤ ρ →
      ∀ X : ℕ → ℝ, (∀ k, 0 ≤ X k) →
      (∀ k, k ≤ n → X k ≤ A * ρ ^ k) →
        flowJetPolynomialEval P X ≤ C * A ^ e * ρ ^ n := by
  induction P with
  | nil =>
    refine ⟨1, 0, le_rfl, ?_⟩
    intro A ρ hA hρ X hX hb
    simp only [flowJetPolynomialEval_nil, pow_zero, one_mul]
    exact pow_nonneg (zero_le_one.trans hρ) n
  | cons m P ih =>
    have hm := hP m List.mem_cons_self
    have ht : FlowJetPolynomialDegreeLE P n :=
      fun a ha => hP a (List.mem_cons_of_mem m ha)
    obtain ⟨C, e, hC, htail⟩ := ih ht
    refine ⟨1 + m.1 + C, m.2.length + e, by linarith only [hm.1, hC], ?_⟩
    intro A ρ hA hρ X hX hb
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
    have hprod : (m.2.map X).prod ≤ A ^ m.2.length * ρ ^ n :=
      (weighted_list_product_le m.2 X hA0 hρ0 hX
        (fun k hk => hb k ((list_member_le_sum m.2 hk).trans hm.2))).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ hm.2)
          (pow_nonneg hA0 m.2.length))
    have hhead : m.1 * (m.2.map X).prod ≤
        m.1 * (A ^ (m.2.length + e) * ρ ^ n) :=
      mul_le_mul_of_nonneg_left
        (hprod.trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hA (by omega)) (pow_nonneg hρ0 n))) hm.1
    have hrest : flowJetPolynomialEval P X ≤
        C * (A ^ (m.2.length + e) * ρ ^ n) := by
      calc
        _ ≤ C * A ^ e * ρ ^ n := htail hA hρ X hX hb
        _ ≤ C * A ^ (m.2.length + e) * ρ ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (by omega))
              (zero_le_one.trans hC)) (pow_nonneg hρ0 n)
        _ = _ := mul_assoc _ _ _
    rw [flowJetPolynomialEval_cons]
    calc
      _ ≤ m.1 * (A ^ (m.2.length + e) * ρ ^ n) +
          C * (A ^ (m.2.length + e) * ρ ^ n) := add_le_add hhead hrest
      _ = (m.1 + C) * (A ^ (m.2.length + e) * ρ ^ n) := by ring
      _ ≤ (1 + m.1 + C) * (A ^ (m.2.length + e) * ρ ^ n) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg (pow_nonneg hA0 _) (pow_nonneg hρ0 _))
      _ = _ := (mul_assoc _ _ _).symm

/-- Uniformly through the requested prefix, an actual order k+1 flow
jet keeps the field's order-minus-one power ρ^k. No bound on a flow jet
is supplied. The unused higher raw bounds do not enter C or e. -/
theorem n04NegativeGeometry_flow_spatial_weighted_prefix (Λ : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧ ∀ {A ρ : ℝ}, 1 ≤ A → 1 ≤ ρ →
      ∀ (F : ℝ × N04FlowPoint → ℝ), ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
      ∀ M : ℕ → ℝ, (∀ j, 0 ≤ M j) → N04FlowPositiveRawBounds M F →
      N04FlowAngularControl F Λ →
      (∀ j, j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1, ∀ q : N04FlowPoint,
        q.1 ∈ n04FlowParameterBox →
        ‖iteratedFDeriv ℝ (j + 1) (fun y : N04FlowPoint => F (t, y)) q‖ ≤ A * ρ ^ j) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ, N04FlowEquations F Θ →
      ∀ k, k ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ q : N04FlowPoint, q.1 ∈ n04FlowParameterBox →
        ‖iteratedFDeriv ℝ (k + 1) (fun y : N04FlowPoint => Θ y.1 t y.2) q‖ ≤
          C * A ^ e * ρ ^ k := by
  classical
  choose P hP hflow using fun k => exists_n04Flow_spatialJet_polynomial Λ k
  choose c e hc hpoly using fun k =>
    n04NegativeGeometry_flowPolynomial_weighted_prefix (P k) k (hP k)
  let C : ℝ := 1 + ∑ i : Fin (N + 1), c i.val
  let d : ℕ := ∑ i : Fin (N + 1), e i.val
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => zero_le_one.trans (hc i.val))
  have hcC (k : ℕ) (hk : k ≤ N) : c k ≤ C :=
    (Finset.single_le_sum (fun i _ => zero_le_one.trans (hc i.val))
      (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)))).trans
      (le_add_of_nonneg_left zero_le_one)
  have hed (k : ℕ) (hk : k ≤ N) : e k ≤ d :=
    Finset.single_le_sum (fun (i : Fin (N + 1)) _ => Nat.zero_le (e i.val))
      (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)))
  refine ⟨C, d, hC, ?_⟩
  intro A ρ hA hρ F hF hperiod M hM hraw hangular hprefix Θ hΘ k hk t ht q hq
  let R : ℕ → ℝ := fun j => if j ≤ N then A * ρ ^ j else M j
  have hR (j : ℕ) : 0 ≤ R j := by
    by_cases hj : j ≤ N
    · simpa only [R, if_pos hj] using
        mul_nonneg (zero_le_one.trans hA) (pow_nonneg (zero_le_one.trans hρ) j)
    · simpa only [R, if_neg hj] using hM j
  have hrawR : N04FlowPositiveRawBounds R F := by
    intro j r hr y hy
    by_cases hj : j ≤ N
    · simpa only [R, if_pos hj] using hprefix j hj r hr y hy
    · simpa only [R, if_neg hj] using hraw j r hr y hy
  have hjet := hflow k R hR F hF hperiod hrawR hangular Θ hΘ t ht q hq
  have hnum : flowJetPolynomialEval (P k) R ≤ c k * A ^ e k * ρ ^ k :=
    hpoly k hA hρ R hR (fun j hj => by
      simp only [R, if_pos (hj.trans hk), le_refl])
  calc
    _ ≤ flowJetPolynomialEval (P k) R := hjet
    _ ≤ c k * A ^ e k * ρ ^ k := hnum
    _ ≤ C * A ^ d * ρ ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hcC k hk) (pow_le_pow_right₀ hA (hed k hk))
          (pow_nonneg (zero_le_one.trans hA) _) (zero_le_one.trans hC))
        (pow_nonneg (zero_le_one.trans hρ) _)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_flow_spatial_weighted_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_flow_spatial_weighted_prefix
