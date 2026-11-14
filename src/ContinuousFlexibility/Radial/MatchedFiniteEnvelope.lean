module

public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# A common spatial envelope for finitely many initial frequency bands

Only constants and coefficient exponents are enlarged. The full spatial
decay and the actual family of quantities remain unchanged. This absorbs
the finitely many modes before the uniform deep-tail threshold.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements

theorem matchedEnvelope_mono {C C' a a' : ℝ}
    (hC : 0 ≤ C) (hCC : C ≤ C') (haa : a ≤ a') (k m : ℕ) :
    C * Real.exp (a * (radialQ k + radialQ m) - |radialS k - radialS m|) ≤
      C' * Real.exp (a' * (radialQ k + radialQ m) - |radialS k - radialS m|) := by
  have he : Real.exp (a * (radialQ k + radialQ m) - |radialS k - radialS m|) ≤
      Real.exp (a' * (radialQ k + radialQ m) - |radialS k - radialS m|) := by
    apply Real.exp_le_exp.mpr
    exact sub_le_sub_right (mul_le_mul_of_nonneg_right haa
      (add_nonneg (radialQ_nonneg k) (radialQ_nonneg m))) _
  exact mul_le_mul hCC he (Real.exp_pos _).le (hC.trans hCC)

theorem matchedEnvelope_finite_family {ι : Type*} [Finite ι]
    (level : ℕ → ℕ) (value : ι → ℕ → ℕ → ℝ)
    (h : ∀ i, ∃ C a : ℝ, 0 < C ∧ 0 ≤ a ∧ ∀ k m,
      value i k m ≤ C * Real.exp
        (a * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|)) :
    ∃ C a : ℝ, 0 < C ∧ 0 ≤ a ∧ ∀ i k m,
      value i k m ≤ C * Real.exp
        (a * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|) := by
  classical
  choose C a hC ha hbound using h
  obtain ⟨C₀, hC₀⟩ := (Set.finite_range C).bddAbove
  obtain ⟨a₀, ha₀⟩ := (Set.finite_range a).bddAbove
  refine ⟨max 1 C₀, max 0 a₀,
    zero_lt_one.trans_le (le_max_left _ _), le_max_left _ _, ?_⟩
  intro i k m
  apply (hbound i k m).trans
  exact matchedEnvelope_mono (hC i).le
    ((hC₀ (mem_range_self i)).trans (le_max_right _ _))
    ((ha₀ (mem_range_self i)).trans (le_max_right _ _)) _ _

/-- Join an initial range and the uniform remaining modes without
changing a single operator or cell label. -/
theorem matchedEnvelope_initial_and_tail
    (level : ℕ → ℕ) (value : ℕ → ℕ → ℕ → ℝ) (N : ℕ)
    (hinitial : ∀ i : Fin N, ∃ C a : ℝ, 0 < C ∧ 0 ≤ a ∧ ∀ k m,
      value i k m ≤ C * Real.exp
        (a * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|))
    {C₁ a₁ : ℝ} (hC₁ : 0 < C₁) (ha₁ : 0 ≤ a₁)
    (htail : ∀ i, N ≤ i → ∀ k m,
      value i k m ≤ C₁ * Real.exp
        (a₁ * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|)) :
    ∃ C a : ℝ, 0 < C ∧ 0 ≤ a ∧ ∀ i k m,
      value i k m ≤ C * Real.exp
        (a * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|) := by
  obtain ⟨C₀, a₀, hC₀, ha₀, h₀⟩ :=
    matchedEnvelope_finite_family level (fun i : Fin N => value i) hinitial
  refine ⟨max C₀ C₁, max a₀ a₁, hC₀.trans_le (le_max_left _ _),
    ha₀.trans (le_max_left _ _), ?_⟩
  intro i k m
  by_cases hi : i < N
  · exact (h₀ ⟨i, hi⟩ k m).trans
      (matchedEnvelope_mono hC₀.le (le_max_left _ _) (le_max_left _ _) _ _)
  · exact (htail i (Nat.le_of_not_gt hi) k m).trans
      (matchedEnvelope_mono hC₁.le (le_max_right _ _) (le_max_right _ _) _ _)

end ContinuousFlexibility.Radial
