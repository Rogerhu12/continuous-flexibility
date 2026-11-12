import ContinuousFlexibility.Analysis.N04PositiveComponents
import Mathlib.Data.Set.Finite.Lattice

/-!
# Recognizing positive components by their actual endpoints

A positive open interval with two zero endpoints is one complete
connected component. Distinct positive components have distinct left
endpoints, so finitely many exceptional left endpoints account for only
finitely many components and give one reciprocal-width bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

theorem n04PositiveLeft_injective {a b : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) :
    Function.Injective (n04PositiveLeft (a := a) (b := b) (f := f)) := by
  intro i j hij
  have hi := (n04PositiveComponent_bounds hf i).2.1
  have hj : n04PositiveLeft i < n04PositiveRight j := by
    rw [hij]
    exact (n04PositiveComponent_bounds hf j).2.1
  obtain ⟨r, hlr, hru⟩ := exists_between (lt_min hi hj)
  have hri : r ∈ i.val := (n04PositiveComponent_mem_iff hf i).mpr
    ⟨hlr, hru.trans_le (min_le_left _ _)⟩
  have hrj : r ∈ j.val := (n04PositiveComponent_mem_iff hf j).mpr
    ⟨by rw [← hij]; exact hlr, hru.trans_le (min_le_right _ _)⟩
  exact Subtype.ext ((n04PositiveComponent_eq_component i hri).trans
    (n04PositiveComponent_eq_component j hrj).symm)

theorem n04PositiveComponent_existsUnique_of_zero_endpoints
    {a b l u : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (ha : a ≤ l) (hlu : l < u) (hb : u ≤ b)
    (hlzero : f l = 0) (huzero : f u = 0)
    (hpos : ∀ r ∈ Ioo l u, 0 < f r) :
    ∃! i : N04PositiveComponent a b f,
      n04PositiveLeft i = l ∧ n04PositiveRight i = u := by
  obtain ⟨r, hlr, hru⟩ := exists_between hlu
  have hsub : Ioo l u ⊆ n04PositiveRegion a b f := by
    intro x hx
    exact ⟨⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩, hpos x hx⟩
  obtain ⟨i, hri, _⟩ :=
    (n04PositiveComponent_existsUnique_mem_iff r).mpr (hsub ⟨hlr, hru⟩)
  have hinside : Ioo l u ⊆ i.val := by
    rw [n04PositiveComponent_eq_component i hri]
    exact isPreconnected_Ioo.subset_connectedComponentIn ⟨hlr, hru⟩ hsub
  rw [n04PositiveComponent_eq_Ioo hf i] at hinside
  have hends := (Ioo_subset_Ioo_iff hlu).mp hinside
  have hl : n04PositiveLeft i = l := le_antisymm hends.1 (le_of_not_gt fun h => by
    have hp := n04PositiveComponent_interval_pos hf i ⟨h, hlu.trans_le hends.2⟩
    exact hp.ne' hlzero)
  have hu : n04PositiveRight i = u := le_antisymm (le_of_not_gt fun h => by
    have hp := n04PositiveComponent_interval_pos hf i ⟨hends.1.trans_lt hlu, h⟩
    exact hp.ne' huzero) hends.2
  refine ⟨i, ⟨hl, hu⟩, ?_⟩
  intro j hj
  exact n04PositiveLeft_injective hf (hj.1.trans hl.symm)

theorem n04PositiveComponent_finite_of_left_mem
    {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {A : Set ℝ} (hA : A.Finite) :
    {i : N04PositiveComponent a b f | n04PositiveLeft i ∈ A}.Finite :=
  Set.Finite.preimage (n04PositiveLeft_injective hf).injOn hA

theorem n04PositiveComponent_width_inverse_bound_of_left_mem
    {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {A : Set ℝ} (hA : A.Finite) :
    ∃ B : ℝ, 0 < B ∧ ∀ i : N04PositiveComponent a b f,
      n04PositiveLeft i ∈ A → (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ B := by
  have hfinite := n04PositiveComponent_finite_of_left_mem hf hA
  obtain ⟨M, hM⟩ := (hfinite.image
    (fun i => (n04PositiveRight i - n04PositiveLeft i)⁻¹)).bddAbove
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro i hi
  exact (hM ⟨i, hi, rfl⟩).trans (le_max_right _ _)

end ContinuousFlexibility.Analysis
