import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bounds on a compact set from interior local bounds

A function need not have prescribed boundary values. Bounds on its values
in an arbitrary subset, valid near each point of a compact set, admit one
bound on the part of that subset lying in the compact set.
-/

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

/-- Local bounds around the closed set control the actual function on
the interior subset, without defining any boundary extension. -/
theorem n07b_exists_bound_on_compact_of_local_bounds
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    {K U : Set X} (hK : IsCompact K) {f : X → E}
    (hf : ∀ x ∈ K, ∃ B : ℝ, ∀ᶠ y in 𝓝 x, y ∈ U → ‖f y‖ ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, x ∈ U → ‖f x‖ ≤ B := by
  classical
  choose B hB using fun x : K => hf x x.2
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover'
    (fun x hx => {y | y ∈ U → ‖f y‖ ≤ B ⟨x, hx⟩})
    (fun x hx => hB ⟨x, hx⟩)
  refine ⟨∑ i ∈ s, max (B i) 0, Finset.sum_nonneg (fun _ _ => le_max_right _ _), ?_⟩
  intro x hx hxU
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  calc
    ‖f x‖ ≤ B i := hxi hxU
    _ ≤ max (B i) 0 := le_max_left _ _
    _ ≤ ∑ j ∈ s, max (B j) 0 :=
      Finset.single_le_sum (fun _ _ => le_max_right _ _) hi

end ContinuousFlexibility.Analysis
