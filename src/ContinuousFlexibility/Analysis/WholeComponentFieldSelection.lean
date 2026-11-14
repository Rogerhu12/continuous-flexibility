module

public import ContinuousFlexibility.Analysis.N04bRootOrientation
public import ContinuousFlexibility.Analysis.N04PositiveComponents

/-!
# Selecting the actual field of a whole component

Closed negative components are disjoint: their simple roots have
opposite derivative signs at the two ends, so two negative components
cannot share an endpoint. The selection below therefore retains the
actual closed root values. On a positive component it selects the
unique positive field. The choice depends only on the physical radius.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem closed_intervals_disjoint_of_open_disjoint {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hbc : b ≠ c) (had : a ≠ d)
    (h : Disjoint (Ioo a b) (Ioo c d)) : Disjoint (Icc a b) (Icc c d) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  by_cases hbc' : b ≤ c
  · exact hbc (le_antisymm hbc' (hy.1.trans hx.2))
  by_cases hda : d ≤ a
  · exact had (le_antisymm (hx.1.trans hy.2) hda)
  have hcb : c < b := lt_of_not_ge hbc'
  have had' : a < d := lt_of_not_ge hda
  have hgap : max a c < min b d :=
    lt_min (max_lt hab hcb) (max_lt had' hcd)
  let y : ℝ := (max a c + min b d) / 2
  have hlo : max a c < y := by dsimp only [y]; linarith
  have hhi : y < min b d := by dsimp only [y]; linarith
  exact Set.disjoint_left.mp h
    ⟨(le_max_left a c).trans_lt hlo, hhi.trans_le (min_le_left b d)⟩
    ⟨(le_max_right a c).trans_lt hlo, hhi.trans_le (min_le_right b d)⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n04_negativeClosed_pairwiseDisjoint
    (hN : N01Properties D T S C base loss ε) :
    Pairwise (fun m n : ℕ =>
      Disjoint (Icc (C.left m) (C.right m)) (Icc (C.left n) (C.right n))) := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  intro m n hmn
  have hm := n04b_component_root_orientations hN m
  have hn := n04b_component_root_orientations hN n
  apply closed_intervals_disjoint_of_open_disjoint (hC.1 m).2.1 (hC.1 n).2.1
  · intro he
    rw [he] at hm
    exact (not_lt_of_ge hm.2.le) hn.1
  · intro he
    rw [he] at hm
    exact (not_lt_of_ge hn.2.le) hm.1
  · exact hC.2.2.1 m n hmn

theorem n04_negativeClosed_index_unique
    (hN : N01Properties D T S C base loss ε) {m n : ℕ} {r : ℝ}
    (hm : r ∈ Icc (C.left m) (C.right m))
    (hn : r ∈ Icc (C.left n) (C.right n)) : m = n := by
  by_contra hne
  exact Set.disjoint_left.mp (n04_negativeClosed_pairwiseDisjoint hN hne) hm hn

theorem n04_profile_nonpos_on_negativeClosed
    (hC : controlGeometryConditions D S C) (m : ℕ) {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) : deriv D.w r ≤ 0 := by
  by_cases hl : r = C.left m
  · rw [hl, (hC.2.1 m).1]
  by_cases hh : r = C.right m
  · rw [hh, (hC.2.1 m).2.1]
  exact (hC.2.2.2.1 m r
    ⟨lt_of_le_of_ne hr.1 (Ne.symm hl), lt_of_le_of_ne hr.2 hh⟩).le

def n04WholeComponentField {E : Type*}
    (C : NonlinearGeometryData S) (Fneg : ℕ → PolarPoint → E)
    (Fpos : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → E)
    (fallback : PolarPoint → E) (p : PolarPoint) : E := by
  classical
  exact if h : ∃ m, p.1 ∈ Icc (C.left m) (C.right m) then
      Fneg (Classical.choose h) p
    else if h : ∃ i : N04PositiveComponent D.a D.b (deriv D.w),
        p.1 ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) then
      Fpos (Classical.choose h) p
    else fallback p

theorem n04WholeComponentField_eq_negative {E : Type*}
    (hN : N01Properties D T S C base loss ε)
    (Fneg : ℕ → PolarPoint → E)
    (Fpos : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → E)
    (fallback : PolarPoint → E) {m : ℕ} {p : PolarPoint}
    (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
    n04WholeComponentField C Fneg Fpos fallback p = Fneg m p := by
  classical
  have hex : ∃ n, p.1 ∈ Icc (C.left n) (C.right n) := ⟨m, hp⟩
  have he : Classical.choose hex = m :=
    n04_negativeClosed_index_unique hN (Classical.choose_spec hex) hp
  simp only [n04WholeComponentField, dif_pos hex, he]

theorem n04WholeComponentField_eq_positive {E : Type*}
    (hf : Continuous (deriv D.w)) (hC : controlGeometryConditions D S C)
    (Fneg : ℕ → PolarPoint → E)
    (Fpos : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → E)
    (fallback : PolarPoint → E)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {p : PolarPoint}
    (hp : p.1 ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i)) :
    n04WholeComponentField C Fneg Fpos fallback p = Fpos i p := by
  classical
  have hn : ¬ ∃ m, p.1 ∈ Icc (C.left m) (C.right m) := by
    rintro ⟨m, hm⟩
    exact (not_lt_of_ge (n04_profile_nonpos_on_negativeClosed hC m hm))
      (n04PositiveComponent_interval_pos hf i hp)
  have hex : ∃ j : N04PositiveComponent D.a D.b (deriv D.w),
      p.1 ∈ Ioo (n04PositiveLeft j) (n04PositiveRight j) := ⟨i, hp⟩
  have he : Classical.choose hex = i := by
    by_contra hne
    exact Set.disjoint_left.mp
      (n04PositiveComponent_interval_pairwiseDisjoint hf hne)
      (Classical.choose_spec hex) hp
  simp only [n04WholeComponentField, dif_neg hn, dif_pos hex, he]

end ContinuousFlexibility.Analysis
