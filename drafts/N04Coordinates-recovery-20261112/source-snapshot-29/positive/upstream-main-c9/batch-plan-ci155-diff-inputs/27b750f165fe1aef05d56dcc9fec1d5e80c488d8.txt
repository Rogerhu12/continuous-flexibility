import ContinuousFlexibility.Analysis.N01cPhysicalGraphNormalization

/-!
# Uniform constants for a finite physical mixed-derivative prefix

The common high index is already fixed by the spatial cutoff and the
parameter prefix. Only the two scalar material constants are enlarged
over the finitely many positive radial and positive parameter orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Finite uniformization changes neither the common domain nor its
high index. The actual estimate is passed as an opaque predicate. -/
theorem n01c_finite_radial_prefix_constants
    (P : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → Prop) (K : ℕ)
    (hmono : ∀ n b k s C A C' A', 1 ≤ C → 0 ≤ A → C ≤ C' → A ≤ A' →
      P n b k s C A → P n b k s C' A')
    (hpoint : ∀ n b k s, 0 < k → k ≤ K → n + 1 + b ≤ s →
      ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ P n b k s C A) :
    ∀ s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ n b k, 0 < k → k ≤ K → n + 1 + b ≤ s → P n b k s C A := by
  classical
  intro s
  let I := Fin (s + 1) × Fin (s + 1) × Fin (K + 1)
  let Q : I → ℝ → ℝ → Prop := fun i C A =>
    0 < i.2.2.val → i.1.val + 1 + i.2.1.val ≤ s →
      P i.1.val i.2.1.val i.2.2.val s C A
  have hQmono : ∀ i C A C' A', 1 ≤ C → 0 ≤ A → C ≤ C' → A ≤ A' →
      Q i C A → Q i C' A' := by
    intro i C A C' A' hC hA hCC hAA hb hk hab
    exact hmono i.1.val i.2.1.val i.2.2.val s C A C' A'
      hC hA hCC hAA (hb hk hab)
  have hQ : ∀ i, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ Q i C A := by
    intro i
    by_cases hk : 0 < i.2.2.val
    · by_cases hab : i.1.val + 1 + i.2.1.val ≤ s
      · obtain ⟨C, A, hC, hA, hb⟩ := hpoint i.1.val i.2.1.val i.2.2.val s
          hk (Nat.le_of_lt_succ i.2.2.isLt) hab
        exact ⟨C, A, hC, hA, fun _ _ => hb⟩
      · exact ⟨1, 0, le_rfl, le_rfl, fun _ h => (hab h).elim⟩
    · exact ⟨1, 0, le_rfl, le_rfl, fun h => (hk h).elim⟩
  obtain ⟨C, A, hC, hA, hb⟩ := exists_finite_graph_materialConstants Q hQmono hQ
  refine ⟨C, A, hC, hA, ?_⟩
  intro n b k hk hkK hab
  let i : I :=
    (⟨n, by omega⟩, ⟨b, by omega⟩, ⟨k, Nat.lt_succ_of_le hkK⟩)
  exact hb i hk hab

end ContinuousFlexibility.Analysis
