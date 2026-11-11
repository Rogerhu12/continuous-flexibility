import ContinuousFlexibility.Radial.MatchedWeightMorseFibers
import ContinuousFlexibility.Radial.ReferenceFiniteIndexFloor

/-!
# Finite level multiplicity after the actual return-margin index floor

The fixed floor merges only finitely many of the original Morse levels.
The middle cell and the two tails give at most 2 N + 3 cells at the
merged level. Saturating cells leaves these indices unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements

theorem morseTwoTailAt_sublevel_fiber_bound (base N : ℕ) :
    Set.Finite {m | morseTwoTailAt base (fun _ k => base + k) m ≤ N} ∧
      Set.ncard {m | morseTwoTailAt base (fun _ k => base + k) m ≤ N} ≤ 2 * N + 3 := by
  classical
  let L := (Finset.range (N + 1)).image (morseTailIndex false)
  let R := (Finset.range (N + 1)).image (morseTailIndex true)
  let s := insert 0 (L ∪ R)
  have hsub : {m | morseTwoTailAt base (fun _ k => base + k) m ≤ N} ⊆ (s : Set ℕ) := by
    intro j hj
    cases j with
    | zero => simp only [s, Finset.mem_coe, Finset.mem_insert, true_or]
    | succ j =>
        let p := Equiv.boolProdNatEquivNat.symm j
        change base + p.2 ≤ N at hj
        have hp : p.2 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
        have he : morseTailIndex p.1 p.2 = j + 1 := by
          unfold morseTailIndex
          rw [Prod.eta p]
          exact congrArg (· + 1) (Equiv.boolProdNatEquivNat.apply_symm_apply j)
        change j + 1 ∈ s
        rw [← he]
        apply Finset.mem_insert_of_mem
        cases hs : p.1
        · apply Finset.mem_union_left
          exact Finset.mem_image.mpr ⟨p.2, hp, by rw [hs]⟩
        · apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨p.2, hp, by rw [hs]⟩
  have hL : L.card ≤ N + 1 := by
    calc
      L.card ≤ (Finset.range (N + 1)).card := Finset.card_image_le
      _ = N + 1 := Finset.card_range _
  have hR : R.card ≤ N + 1 := by
    calc
      R.card ≤ (Finset.range (N + 1)).card := Finset.card_image_le
      _ = N + 1 := Finset.card_range _
  have hs : s.card ≤ 2 * N + 3 := by
    have hi : s.card ≤ (L ∪ R).card + 1 := Finset.card_insert_le _ _
    have hu : (L ∪ R).card ≤ L.card + R.card := Finset.card_union_le _ _
    omega
  refine ⟨s.finite_toSet.subset hsub, ?_⟩
  have hn := Set.ncard_le_ncard hsub s.finite_toSet
  rw [Set.ncard_coe_finset] at hn
  exact hn.trans hs

theorem morseTwoTailAt_floor_level_fiber_bound (base N n : ℕ) :
    Set.Finite {m | max (morseTwoTailAt base (fun _ k => base + k) m) N = n} ∧
      Set.ncard {m | max (morseTwoTailAt base (fun _ k => base + k) m) N = n} ≤
        2 * N + 3 := by
  by_cases hn : n = N
  · subst n
    have he : {m | max (morseTwoTailAt base (fun _ k => base + k) m) N = N} =
        {m | morseTwoTailAt base (fun _ k => base + k) m ≤ N} := by
      ext m
      simp only [Set.mem_setOf_eq, max_eq_right_iff]
    rw [he]
    exact morseTwoTailAt_sublevel_fiber_bound base N
  · have hsub : {m | max (morseTwoTailAt base (fun _ k => base + k) m) N = n} ⊆
        {m | morseTwoTailAt base (fun _ k => base + k) m = n} := by
      intro m hm
      change max (morseTwoTailAt base (fun _ k => base + k) m) N = n at hm
      change morseTwoTailAt base (fun _ k => base + k) m = n
      omega
    obtain ⟨hf, hc⟩ := morseTwoTailAt_level_fiber_bound base n
    refine ⟨hf.subset hsub, (Set.ncard_le_ncard hsub hf).trans (hc.trans ?_)⟩
    omega

end ContinuousFlexibility.Radial
