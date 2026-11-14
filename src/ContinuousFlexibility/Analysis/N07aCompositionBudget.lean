module

public import ContinuousFlexibility.Analysis.N07aFiniteParameterProduct
public import ContinuousFlexibility.Analysis.OneHighCompositionJets
public import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# The actual chain-rule derivative budget

A partition with k blocks has k source derivatives. Charging each chart
factor only its order minus one leaves total order exactly n. The first
chart derivative is part of the fixed offset, not a loss repeated k times.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n07a_partition_source_order {n : ℕ} (c : OrderedFinpartition n) :
    c.length + (∑ j, (c.partSize j - 1)) = n := by
  have h : (∑ j, ((c.partSize j - 1) + 1)) = n := by
    calc
      _ = ∑ j, c.partSize j := Finset.sum_congr rfl fun j _ =>
        Nat.sub_add_cancel (c.partSize_pos j)
      _ = n := oneHighPartition_sum_orders c
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, Nat.add_comm] using h

theorem n07a_mixedDerivative_norm_le_iteratedFDeriv
    {U : Set PolarPoint} (hU : IsOpen U) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (a b : ℕ) {x : PolarPoint} (hx : x ∈ U) :
    |mixedDerivative a b f x| ≤ ‖iteratedFDeriv ℝ (a + b) f x‖ := by
  classical
  let w : Fin (a + b) → Fin 2 :=
    Fin.addCases (fun _ : Fin a => 0) (fun _ : Fin b => 1)
  have hr : (∑ i, if w i = 0 then 1 else 0) = a := by
    rw [Fin.sum_univ_add]
    simp [w]
  have hθ : (∑ i, if w i = 0 then 0 else 1) = b := by
    rw [Fin.sum_univ_add]
    simp [w]
  have he := iteratedFDeriv_cylinderBasis_eq_mixedDerivative hU hf (a + b) hx w
  rw [hr, hθ] at he
  have hb (i : Fin (a + b)) : ‖cylinderBasisVector (w i)‖ ≤ (1 : ℝ) := by
    simp only [cylinderBasisVector]
    split <;> norm_num [Prod.norm_def]
  have h := (iteratedFDeriv ℝ (a + b) f x).le_opNorm_mul_prod_of_le hb
  simpa only [he, Finset.prod_const_one, mul_one, Real.norm_eq_abs] using h

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The same base and loss cover every actual Faà di Bruno partition. -/
theorem n07a_chainrule_oneHigh_product
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasSmoothing p) (hIq : HasSmoothing q) (d : ℕ) :
    ∃ base loss : ℕ, ∀ (n t : ℕ) (c : OrderedFinpartition n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E, p base z ≤ 1 → ∀ f : F,
        q (t + c.length + d) f *
          (∏ j, (1 + p ((c.partSize j - 1) + d) z)) ≤
        C * (q (t + n + loss) f + (1 + p (t + n + loss) z) * q base f) := by
  obtain ⟨base, loss, hprod⟩ := n07a_finite_parameter_source_product p q hp hq hIp hIq d
  refine ⟨base, loss, fun n t c => ?_⟩
  exact hprod c.length (fun j => c.partSize j - 1) (t + c.length) (t + n)
    (by have h := n07a_partition_source_order c; omega)

end ContinuousFlexibility.Analysis
