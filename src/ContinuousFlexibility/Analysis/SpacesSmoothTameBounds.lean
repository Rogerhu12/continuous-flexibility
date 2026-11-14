module

public import ContinuousFlexibility.Statements.Analysis

/-!
# Smooth tame bounds from a raw derivative kernel

A genuine directional tower and a pointwise identification with a raw
kernel turn fixed low-seminorm bounds into the local estimates required
by smooth tameness. The conversion takes place on abstract vector spaces,
so specializing the theorem never unfolds a concrete weak-jet tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

/-- Fixed kernel bounds give smooth tameness of an identified genuine
directional tower, with one fixed loss and base for every order. -/
theorem spaces_smoothTameOn_univ_of_kernel_bounds {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) {f : E → F}
    (J : Statements.SmoothDirections Set.univ f)
    (B : ∀ k : ℕ, E → (Fin k → E) → F)
    (hJD : ∀ k x v, J.D k x v = B k x v)
    (base loss : ℕ)
    (hb : ∀ k s : ℕ, ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ R → ∀ v : Fin k → E,
        q s (B k x v) ≤ C *
          ((1 + p (s + loss) x) * ∏ i, p base (v i) +
            ∑ i, p (s + loss) (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j))) :
    Statements.SmoothTameOn p q Set.univ f := by
  refine ⟨J, fun k x₀ _ => ⟨loss, base, 1, zero_lt_one, fun s _ => ?_⟩⟩
  have hR : 1 ≤ 1 + p base x₀ := by
    have h := apply_nonneg (p base) x₀
    linarith
  obtain ⟨C, hC, hbound⟩ := hb k s (1 + p base x₀) hR
  refine ⟨C, hC, fun x _ hx v => ?_⟩
  have hbase : p base x ≤ 1 + p base x₀ := by
    calc
      p base x = p base ((x - x₀) + x₀) := by rw [sub_add_cancel]
      _ ≤ p base (x - x₀) + p base x₀ := map_add_le_add (p base) _ _
      _ ≤ 1 + p base x₀ := add_le_add hx.le le_rfl
  rw [hJD k x v]
  exact hbound x hbase v

end ContinuousFlexibility.Analysis
