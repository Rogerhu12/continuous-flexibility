import ContinuousFlexibility.Analysis.N06NaturalPieceFiniteness
import ContinuousFlexibility.Analysis.N06PhysicalReconstruction

/-!
# Local finiteness of the actual negative canonical pieces

N04's two half-pieces cover each actual negative component retained by
N01. Disjointness of the open physical pieces leaves no additional
negative pieces. Compact finiteness of the natural components therefore
gives compact finiteness of the actual negative pieces, with no extra
assumption on the canonical atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n06_physicalPiece_eq_of_commonPoint
    (hN04 : N04Properties D T S C L K base loss ε)
    {m n : ℕ} {r : ℝ}
    (hm : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m))
    (hn : r ∈ Ioo (K.physicalLeft n) (K.physicalRight n)) : m = n := by
  by_contra hne
  exact (Set.disjoint_left.mp (n06_physicalPiece_pairwiseDisjoint hN04 hne)) hm hn

/-- Every negative canonical piece is one of the two prescribed halves
of an actual N01 negative component. -/
theorem n06_negativePiece_is_cutHalf
    (hN04 : N04Properties D T S C L K base loss ε)
    (hC : controlGeometryConditions D S C) {m : ℕ} (hm : K.positive m = false) :
    ∃ n, m = (K.cutPair n).1 ∨ m = (K.cutPair n).2 := by
  have hfull := hN04
  obtain ⟨_, _, _, hpieces, _, hnegative, _, _, _, _, _, hcut, _⟩ := hfull
  obtain ⟨r, hr⟩ := Set.nonempty_Ioo.mpr (hpieces m).1
  obtain ⟨n, hn⟩ := hC.2.2.2.2.1 r ((hpieces m).2.2 hr) (hnegative m hm r hr)
  obtain ⟨_, _, hleft, hright, hmid, _⟩ := hcut n
  by_cases hrmid : r ≤ K.physicalRight (K.cutPair n).1
  · have hlo : max (K.physicalLeft m) (C.left n) < r := max_lt hr.1 hn.1
    have hhi : r ≤ min (K.physicalRight m) (K.physicalRight (K.cutPair n).1) :=
      le_min hr.2.le hrmid
    obtain ⟨x, hxlo, hxhi⟩ := exists_between (hlo.trans_le hhi)
    have hxm : x ∈ Ioo (K.physicalLeft m) (K.physicalRight m) :=
      ⟨(le_max_left _ _).trans_lt hxlo, hxhi.trans_le (min_le_left _ _)⟩
    have hxn : x ∈ Ioo (K.physicalLeft (K.cutPair n).1)
        (K.physicalRight (K.cutPair n).1) := by
      rw [hleft]
      exact ⟨(le_max_right _ _).trans_lt hxlo, hxhi.trans_le (min_le_right _ _)⟩
    exact ⟨n, Or.inl (n06_physicalPiece_eq_of_commonPoint hN04 hxm hxn)⟩
  · have hxn : r ∈ Ioo (K.physicalLeft (K.cutPair n).2)
        (K.physicalRight (K.cutPair n).2) := by
      rw [← hmid, hright]
      exact ⟨lt_of_not_ge hrmid, hn.2⟩
    exact ⟨n, Or.inr (n06_physicalPiece_eq_of_commonPoint hN04 hr hxn)⟩

theorem n06_cutHalf_closed_subset_component
    (hN04 : N04Properties D T S C L K base loss ε) (n : ℕ) :
    Icc (K.physicalLeft (K.cutPair n).1) (K.physicalRight (K.cutPair n).1) ⊆
      Icc (C.left n) (C.right n) ∧
    Icc (K.physicalLeft (K.cutPair n).2) (K.physicalRight (K.cutPair n).2) ⊆
      Icc (C.left n) (C.right n) := by
  obtain ⟨_, _, _, hpieces, _, _, _, _, _, _, _, hcut, _⟩ := hN04
  obtain ⟨_, _, hleft, hright, hmid, _⟩ := hcut n
  have hl := (hpieces (K.cutPair n).1).1
  have hr := (hpieces (K.cutPair n).2).1
  rw [hleft, hmid] at hl
  rw [hright] at hr
  constructor
  · intro x hx
    rw [hleft, hmid] at hx
    exact ⟨hx.1, hx.2.trans hr.le⟩
  · intro x hx
    rw [hright] at hx
    exact ⟨hl.le.trans hx.1, hx.2⟩

/-- The actual negative piece closures meet a compact interior support
only finitely often. This follows from the existing N01/N04 contracts. -/
theorem n06_negativePieces_finite_on_compact
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (hN04 : N04Properties D T S C L K base loss ε)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    {m | K.positive m = false ∧
      (Icc (K.physicalLeft m) (K.physicalRight m) ∩ J).Nonempty}.Finite := by
  have hfinite := n06_controlComponents_finite_on_compact hD hC hJ hJD
  apply ((hfinite.image (fun n => (K.cutPair n).1)).union
    (hfinite.image (fun n => (K.cutPair n).2))).subset
  intro m hm
  obtain ⟨n, hmn | hmn⟩ := n06_negativePiece_is_cutHalf hN04 hC hm.1
  · left
    refine ⟨n, ?_, hmn.symm⟩
    obtain ⟨x, hx, hxJ⟩ := hm.2
    rw [hmn] at hx
    exact ⟨x, (n06_cutHalf_closed_subset_component hN04 n).1 hx, hxJ⟩
  · right
    refine ⟨n, ?_, hmn.symm⟩
    obtain ⟨x, hx, hxJ⟩ := hm.2
    rw [hmn] at hx
    exact ⟨x, (n06_cutHalf_closed_subset_component hN04 n).2 hx, hxJ⟩

end ContinuousFlexibility.Statements
