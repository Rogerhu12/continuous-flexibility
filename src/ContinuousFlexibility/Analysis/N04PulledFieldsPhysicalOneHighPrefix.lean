module

public import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalPrefixPower

/-!
# Physical prefixes from one-high estimates on a small state set

The raw low order is selected once, before the parameter order. Its
small-state condition is part of the abstract set used for interpolation.
The resulting prefix retains one low order for the whole field family.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- Conditional small-state one-high bounds yield a common physical
prefix. The parameter-order loss is converted to a prefix offset, and
the low order may be required to dominate an existing neighborhood. -/
theorem n04PulledFields_physicalPrefix_of_smallOneHigh
    {U : Set X} (T : ∀ k : ℕ, ι → ℕ → ℕ → X → (Fin k → X) → ℝ)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (requestedBase : ℕ) (E H : ι → ℝ)
    (hE : ∀ i, 1 ≤ E i) (hH : ∀ i, 0 ≤ H i)
    (hjet : ∃ rawBase : ℕ, ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ i a b, a + b ≤ s →
      ∀ x ∈ U, p rawBase x ≤ 1 → ∀ v : Fin k → X,
        |T k i a b x v| ≤ B * E i ^ B * parameterHeightWeight (H i) k *
          oneHighVariationWeight p rawBase (s + loss) x v) :
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ K : ℕ, ∃ offset : ℕ,
      ∀ top : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ top →
      ∀ i x, x ∈ U → p base x ≤ 1 → ∀ v : Fin k → X,
      (∀ d, p base (v d) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (top + (base + offset + 1)) x ≤ R →
      (∀ d, p (top + (base + offset + 1)) (v d) ≤ R) →
        |T k i a b x v| ≤ C * E i ^ A * parameterHeightWeight (H i) k *
          (R ^ (1 / ((top : ℝ) + 1))) ^ (a + b + offset) := by
  classical
  refine hjet.elim fun rawBase hraw => ?_
  let L : ℕ → ℕ := fun k => (hraw k).choose
  have hprefix := n04PulledFields_physicalPrefix_of_oneHigh
    (U := {x | x ∈ U ∧ p rawBase x ≤ 1}) T p hp hI rawBase L E H hE hH
    (fun k s => ⟨((hraw k).choose_spec s).choose,
      ((hraw k).choose_spec s).choose_spec.1,
      fun i a b hab x hx v =>
        ((hraw k).choose_spec s).choose_spec.2 i a b hab x hx.1 hx.2 v⟩)
  refine hprefix.elim fun low hlow => ?_
  let base : ℕ := max requestedBase low
  have hlowbase : low ≤ base := le_max_right _ _
  refine ⟨base, le_max_left _ _, fun K => ?_⟩
  refine (hlow.2 K).elim fun offset hoffset => ⟨offset, fun top => ?_⟩
  refine (hoffset top).elim fun C hC => hC.elim fun A hCA => ?_
  refine ⟨C, A, hCA.1, hCA.2.1, ?_⟩
  intro k hk a b hab i x hx hxsmall v hv R hR hxR hvR
  have hxlow : p low x ≤ 1 := (hp hlowbase x).trans hxsmall
  have hhigh : top + (low + offset + 1) ≤ top + (base + offset + 1) := by omega
  exact hCA.2.2 k hk a b hab i x ⟨hx, (hp hlow.1 x).trans hxlow⟩ hxlow v
    (fun d => (hp hlowbase (v d)).trans (hv d)) R hR
    ((hp hhigh x).trans hxR) (fun d => (hp hhigh (v d)).trans (hvR d))

end ContinuousFlexibility.Analysis
