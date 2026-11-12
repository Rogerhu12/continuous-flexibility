import ContinuousFlexibility.Analysis.N07aFiniteParameterProduct
import Mathlib.Data.List.OfFn

/-!
# Multiplying a source estimate by the complete finite coefficient product

Both terms in the source estimate use the same interpolation choice. The
parameter factor already present in its low-source term is included in
the derivative budget before the product is bounded.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

theorem n07a_finite_oneHigh_source_product
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasSmoothing p) (hIq : HasSmoothing q) (d : ℕ) :
    ∃ low loss : ℕ, ∀ (n : ℕ) (order : Fin n → ℕ) (t s : ℕ),
      t + (∑ i, order i) ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z : E, p low z ≤ 1 → ∀ u : F,
          (q (t + d) u + (1 + p (t + d) z) * q d u) *
            (∏ i, (1 + p (order i + d) z)) ≤
              C * (q (s + loss) u + (1 + p (s + loss) z) * q low u) := by
  obtain ⟨low, loss, hb⟩ := n07a_finite_parameter_source_product p q hp hq hIp hIq d
  refine ⟨low, loss, fun n order t s hts => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := hb n order t s hts
  obtain ⟨C₂, hC₂, h₂⟩ := hb (n + 1) (Fin.cases t order) 0 s
    (by simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, zero_add] using hts)
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun z hz u => ?_⟩
  have hh₁ := h₁ z hz u
  have hh₂ := h₂ z hz u
  simp only [zero_add, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ] at hh₂
  calc
    _ = q (t + d) u * (∏ i, (1 + p (order i + d) z)) +
        q d u * ((1 + p (t + d) z) * (∏ i, (1 + p (order i + d) z))) := by ring
    _ ≤ C₁ * (q (s + loss) u + (1 + p (s + loss) z) * q low u) +
        C₂ * (q (s + loss) u + (1 + p (s + loss) z) * q low u) := add_le_add hh₁ hh₂
    _ = _ := by ring

theorem n07a_list_oneHigh_source_product
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasSmoothing p) (hIq : HasSmoothing q) (d : ℕ) :
    ∃ low loss : ℕ, ∀ (order : List ℕ) (t s : ℕ),
      t + order.sum ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z : E, p low z ≤ 1 → ∀ u : F,
          (q (t + d) u + (1 + p (t + d) z) * q d u) *
            (order.map (fun j => 1 + p (j + d) z)).prod ≤
              C * (q (s + loss) u + (1 + p (s + loss) z) * q low u) := by
  obtain ⟨low, loss, hb⟩ := n07a_finite_oneHigh_source_product p q hp hq hIp hIq d
  refine ⟨low, loss, fun order t s hts => ?_⟩
  have hsum : (∑ i : Fin order.length, order[i.val]) = order.sum := by
    rw [← Fin.sum_ofFn, List.ofFn_getElem]
  obtain ⟨C, hC, hCb⟩ := hb order.length (fun i => order[i.val]) t s
    (by simpa only [hsum] using hts)
  refine ⟨C, hC, fun z hz u => ?_⟩
  have hprod : (∏ i : Fin order.length, (1 + p (order[i.val] + d) z)) =
      (order.map (fun j => 1 + p (j + d) z)).prod := by
    rw [← Fin.prod_ofFn]
    exact congrArg List.prod
      (List.ofFn_getElem_eq_map order (fun j : ℕ => 1 + p (j + d) z))
  simpa only [hprod] using hCb z hz u

end ContinuousFlexibility.Analysis
