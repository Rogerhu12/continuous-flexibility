import ContinuousFlexibility.Analysis.N04SignedPieces

/-!
# Reference negative halves at an arbitrary genuine interior cut

The original component enumeration is retained. Only its splitting radius
is parameterized; no physical midpoint condition is imposed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {S : PhysicalSpacesData}

def n04bNegativeLeft (C : NonlinearGeometryData S) (cut : ℕ → ℝ)
    (i : ℕ × Bool) : ℝ :=
  if i.2 then cut i.1 else C.left i.1

def n04bNegativeRight (C : NonlinearGeometryData S) (cut : ℕ → ℝ)
    (i : ℕ × Bool) : ℝ :=
  if i.2 then C.right i.1 else cut i.1

variable {C : NonlinearGeometryData S} {cut : ℕ → ℝ}

theorem n04b_negativeHalf_bounds
    (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) (i : ℕ × Bool) :
    D.a < n04bNegativeLeft C cut i ∧
      n04bNegativeLeft C cut i < n04bNegativeRight C cut i ∧
      n04bNegativeRight C cut i < D.b := by
  obtain ⟨m, side⟩ := i
  obtain ⟨ha, _, hb⟩ := hC.1 m
  cases side with
  | false => exact ⟨ha, (hcut m).1, (hcut m).2.trans hb⟩
  | true => exact ⟨ha.trans (hcut m).1, (hcut m).2, hb⟩

theorem n04b_negativeHalf_subset
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) (i : ℕ × Bool) :
    Ioo (n04bNegativeLeft C cut i) (n04bNegativeRight C cut i) ⊆
      Ioo (C.left i.1) (C.right i.1) := by
  obtain ⟨m, side⟩ := i
  intro r hr
  cases side with
  | false => exact ⟨hr.1, hr.2.trans (hcut m).2⟩
  | true => exact ⟨(hcut m).1.trans hr.1, hr.2⟩

theorem n04b_negativeHalf_negative
    (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) (i : ℕ × Bool)
    {r : ℝ} (hr : r ∈ Ioo (n04bNegativeLeft C cut i) (n04bNegativeRight C cut i)) :
    deriv D.w r < 0 :=
  hC.2.2.2.1 i.1 r (n04b_negativeHalf_subset hcut i hr)

theorem n04b_negativeHalf_index_unique
    (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
    {i j : ℕ × Bool} {r : ℝ}
    (hi : r ∈ Ioo (n04bNegativeLeft C cut i) (n04bNegativeRight C cut i))
    (hj : r ∈ Ioo (n04bNegativeLeft C cut j) (n04bNegativeRight C cut j)) :
    i = j := by
  obtain ⟨m, side⟩ := i
  obtain ⟨n, other⟩ := j
  have hmn : m = n := by
    by_contra hne
    exact Set.disjoint_left.mp (hC.2.2.1 m n hne)
      (n04b_negativeHalf_subset hcut (m, side) hi)
      (n04b_negativeHalf_subset hcut (n, other) hj)
  subst n
  cases side <;> cases other
  · rfl
  · exact (lt_asymm hi.2 hj.1).elim
  · exact (lt_asymm hj.2 hi.1).elim
  · rfl

/-- Every point of the original component except its specified cut lies
in exactly one of the two parameterized halves. -/
theorem n04b_negativeHalf_existsUnique
    (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
    {m : ℕ} {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m))
    (hne : r ≠ cut m) :
    ∃! i : ℕ × Bool,
      r ∈ Ioo (n04bNegativeLeft C cut i) (n04bNegativeRight C cut i) := by
  have hex : ∃ i : ℕ × Bool,
      r ∈ Ioo (n04bNegativeLeft C cut i) (n04bNegativeRight C cut i) := by
    rcases lt_or_gt_of_ne hne with hl | hr'
    · exact ⟨(m, false), hr.1, hl⟩
    · exact ⟨(m, true), hr', hr.2⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun j hj => n04b_negativeHalf_index_unique hC hcut hj hi⟩

end ContinuousFlexibility.Analysis
