module

public import ContinuousFlexibility.Analysis.N07aFiniteParameterProduct

/-!
# Arbitrary finite products of the same state grading

The number of factors affects the constant only. One low-order ball and
one fixed loss suffice for every distribution of the derivative budget.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

theorem n07a_finite_state_product
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasSmoothing p) (d : ℕ) :
    ∃ base loss : ℕ, ∀ (n : ℕ) (order : Fin n → ℕ) (s : ℕ),
      (∑ i, order i) ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z : E, p base z ≤ 1 →
          (∏ i, (1 + p (order i + d) z)) ≤ C * (1 + p (s + loss) z) := by
  obtain ⟨base, loss, hb⟩ := n07a_finite_parameter_source_product p realGrading hp
    (fun _ _ _ => le_rfl) hIp hasSmoothing_realGrading d
  refine ⟨base, loss, fun n order s hs => ?_⟩
  obtain ⟨C, hC, hCb⟩ := hb n order 0 s (by simpa only [Nat.zero_add] using hs)
  refine ⟨2 * C, by positivity, fun z hz => ?_⟩
  have h := hCb z hz (1 : ℝ)
  have hnorm (j : ℕ) : realGrading j (1 : ℝ) = 1 := by
    change ‖(1 : ℝ)‖ = 1
    exact norm_one
  simp only [hnorm, one_mul, mul_one] at h
  apply h.trans
  have hp0 := apply_nonneg (p (s + loss)) z
  nlinarith only [hp0, hC, mul_nonneg hp0 hC]

end ContinuousFlexibility.Analysis
