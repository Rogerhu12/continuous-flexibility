import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
import ContinuousFlexibility.Analysis.N05PhysicalPieces

/-!
# Every negative physical piece belongs to a named cut pair

The named pair covers each N01 negative component away from its cut.
Pointwise disjointness of the N04 physical intervals then forces any
negative piece to be one of these halves.  If the initial point is the
cut itself, a nearby point in the same open piece selects a half.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- The original geometric clauses already give a complete enumeration of
the negative pieces by the named cut halves. -/
theorem n05_negative_piece_is_cut_half
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hgeom : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) :
    ∃ m : ℕ, i = (K.cutPair m).1 ∨ i = (K.cutPair m).2 := by
  have hpieces := h04.1.referenceBounds
  have hnegative := h04.1.referenceNegative
  have hcuts := h04.2.1.1.1
  obtain ⟨x, hx⟩ := nonempty_Ioo.mpr (hpieces i).1
  have hxD : x ∈ radialCore D := (hpieces i).2.2 hx
  obtain ⟨m, hxm⟩ := hgeom.2.2.2.2.1 x hxD (hnegative i hi x hx)
  obtain ⟨_, _, hleft, hright, hmeet, _⟩ := hcuts m
  by_cases hxc : x ≤ K.physicalRight (K.cutPair m).1
  · obtain ⟨y, hylo, hyx⟩ := exists_between (max_lt hx.1 hxm.1)
    have hyi : y ∈ Ioo (K.physicalLeft i) (K.physicalRight i) :=
      ⟨(le_max_left _ _).trans_lt hylo, hyx.trans hx.2⟩
    have hyl : y ∈ Ioo (K.physicalLeft (K.cutPair m).1)
        (K.physicalRight (K.cutPair m).1) := by
      constructor
      · rw [hleft]
        exact (le_max_right _ _).trans_lt hylo
      · exact hyx.trans_le hxc
    exact ⟨m, Or.inl ((n05PhysicalPieceIndex_eq h04 hyi).symm.trans
      (n05PhysicalPieceIndex_eq h04 hyl))⟩
  · have hxr : x ∈ Ioo (K.physicalLeft (K.cutPair m).2)
        (K.physicalRight (K.cutPair m).2) := by
      constructor
      · rw [← hmeet]
        exact lt_of_not_ge hxc
      · rw [hright]
        exact hxm.2
    exact ⟨m, Or.inr ((n05PhysicalPieceIndex_eq h04 hx).symm.trans
      (n05PhysicalPieceIndex_eq h04 hxr))⟩

end ContinuousFlexibility.Statements
