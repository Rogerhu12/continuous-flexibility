module

public import ContinuousFlexibility.Analysis.PointwiseProductMaterialJets
public import ContinuousFlexibility.Analysis.FlowJetMaterialClosure
public import ContinuousFlexibility.Analysis.FlowJetPartitionPolynomial

/-!
# Polynomial material cost of a product at one actual point

The genuine local Leibniz inequality records derivative weights i and
n-i, including zero-order factors. The existing weighted polynomial
closure therefore keeps one common state loss at every output order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem exists_ordinaryProduct_material_majorant (n : ℕ) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P n ∧
      ∀ X : ℕ → ℝ, flowJetPolynomialEval P X =
        ∑ i : Fin (n + 1), (n.choose i : ℝ) * X i * X (n - i) := by
  classical
  let Q : Fin (n + 1) → FlowJetPolynomial := fun i =>
    [((n.choose i : ℝ), [(i : ℕ), n - i])]
  have hQ (i : Fin (n + 1)) : FlowJetPolynomialDegreeLE (Q i) n := by
    intro m hm
    have he : m = ((n.choose i : ℝ), [(i : ℕ), n - i]) := List.mem_singleton.mp hm
    rw [he]
    refine ⟨Nat.cast_nonneg _, ?_⟩
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
    have hi := i.isLt
    omega
  obtain ⟨P, hP, heP⟩ := flowJetPolynomial_exists_finite_sum Q n hQ
  refine ⟨P, hP, ?_⟩
  intro X
  rw [heP X]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Q, flowJetPolynomialEval_cons, flowJetPolynomialEval_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, add_zero]
  ring

theorem pointwiseProduct_polynomial_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ f g : X → ℝ, ∀ x : X,
        ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g x →
        (∀ n, ‖iteratedFDeriv ℝ n f x‖ ≤
          A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
        (∀ n, ‖iteratedFDeriv ℝ n g x‖ ≤
          A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
        ∀ n, ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
          B n * W ^ (B n) * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, hmaterial⟩ := flowJetPolynomial_le_material_one_high hp hI inputLoss
  choose P hP heP using exists_ordinaryProduct_material_majorant
  refine ⟨base, loss, ?_⟩
  intro A hA
  choose B hB hbound using fun n => hmaterial n (P n) (hP n) A hA
  refine ⟨B, hB, ?_⟩
  intro z hz W hW f g x hf hg hfj hgj n
  let M : ℕ → ℝ := fun k => A k * W ^ (A k) * (1 + p (k + inputLoss) z)
  have hM (k : ℕ) : 0 ≤ M k := mul_nonneg
    (mul_nonneg (zero_le_one.trans (hA k)) (Real.rpow_nonneg (zero_le_one.trans hW) _))
    (add_nonneg zero_le_one (apply_nonneg _ _))
  have hstart := norm_iteratedFDeriv_mul_le_at hf hg n
  rw [Finset.sum_range] at hstart
  apply hstart.trans
  calc
    _ ≤ ∑ i : Fin (n + 1), (n.choose i : ℝ) * M i * M (n - i) := by
      apply Finset.sum_le_sum
      intro i _
      have hc : 0 ≤ (n.choose (i : ℕ) : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfj i) hc) (hgj (n - i))
        (norm_nonneg _) (mul_nonneg hc (hM i))
    _ = flowJetPolynomialEval (P n) M := (heP n M).symm
    _ ≤ B n * W ^ (B n) * (1 + p (n + loss) z) := hbound n z hz W hW

end ContinuousFlexibility.Analysis
