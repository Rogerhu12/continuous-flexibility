import ContinuousFlexibility.Analysis.N01NeighborhoodRestriction

/-! Global one-high jet estimates give the frozen local tame bounds. -/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {U : Set E} {f : E → F}

theorem smoothTameOn_of_global_oneHigh_jet_bounds
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (J : SmoothDirections U f)
    (hbound : ∀ k, ∃ loss base : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ U, ∀ v : Fin k → E,
        q s (J.D k x v) ≤ C * oneHighVariationWeight p base (s + loss) x v) :
    SmoothTameOn p q U f := by
  refine ⟨J, ?_⟩
  intro k x₀ hx₀
  obtain ⟨loss, base, hb⟩ := hbound k
  refine ⟨loss, base, 1, zero_lt_one, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCs⟩ := hb s
  exact ⟨C, hC, fun x hx _ v => hCs x hx v⟩

end ContinuousFlexibility.Statements
