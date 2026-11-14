module

public import ContinuousFlexibility.Analysis.N06NaturalPieceFiniteness
public import ContinuousFlexibility.Analysis.N06PhysicalReconstruction

/-!
# Local finiteness of the actual negative canonical pieces

The reference partition identifies every negative index with one of the
two prescribed halves of an original N01 component.  At a current state
the actual two-dimensional halves remain inside that same component,
even when their middle cut moves. Compact finiteness of the original
components therefore controls the actual current piece closures.
-/

@[expose] public section

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
  have hpieces := hN04.1.referenceBounds
  have hnegative := hN04.1.referenceNegative
  have hcut := hN04.2.1.1.1
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
  have hpieces := hN04.1.referenceBounds
  have hcut := hN04.2.1.1.1
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

/-- The reference negative interval closures meet a compact support only
finitely often. Current moving domains are treated separately below. -/
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

/-- The two current halves lie in their original negative component.
This uses the literal planar union clause, not the reference middle radius. -/
theorem n06_currentCutHalf_subset_component
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (n : ℕ) :
    physicalPieceOpen S K z (K.cutPair n).1 ⊆
        Ioo (C.left n) (C.right n) ×ˢ (univ : Set ℝ) ∧
      physicalPieceOpen S K z (K.cutPair n).2 ⊆
        Ioo (C.left n) (C.right n) ×ˢ (univ : Set ℝ) := by
  have hcut := hN04.2.1.1.2 z hz hs n
  have hunion := hcut.2.2.2.1
  constructor
  · intro p hp
    have hu : p ∈ physicalPieceOpen S K z (K.cutPair n).1 ∪
        physicalPieceOpen S K z (K.cutPair n).2 := Or.inl hp
    rw [hunion] at hu
    exact hu.1
  · intro p hp
    have hu : p ∈ physicalPieceOpen S K z (K.cutPair n).1 ∪
        physicalPieceOpen S K z (K.cutPair n).2 := Or.inr hp
    rw [hunion] at hu
    exact hu.1

/-- The closure of either moving half stays in the closed original
component, including its two genuine root circles. -/
theorem n06_currentCutHalf_closed_subset_component
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (n : ℕ) :
    physicalPieceClosed S K z (K.cutPair n).1 ⊆
        Icc (C.left n) (C.right n) ×ˢ (univ : Set ℝ) ∧
      physicalPieceClosed S K z (K.cutPair n).2 ⊆
        Icc (C.left n) (C.right n) ×ˢ (univ : Set ℝ) := by
  have hsub := n06_currentCutHalf_subset_component hN04 hz hs n
  constructor
  · apply closure_minimal ?_ (isClosed_Icc.prod isClosed_univ)
    intro p hp
    have h := hsub.1 hp
    exact ⟨⟨h.1.1.le, h.1.2.le⟩, mem_univ _⟩
  · apply closure_minimal ?_ (isClosed_Icc.prod isClosed_univ)
    intro p hp
    have h := hsub.2 hp
    exact ⟨⟨h.1.1.le, h.1.2.le⟩, mem_univ _⟩

/-- A compact radial support meets only finitely many actual current
negative closures. Both moving halves are charged to their fixed original
component; no radial shape of the middle cut is assumed. -/
theorem n06_currentNegativePieces_finite_on_compact
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    {m | K.positive m = false ∧
      (physicalPieceClosed S K z m ∩ (J ×ˢ (univ : Set ℝ))).Nonempty}.Finite := by
  have hfinite := n06_controlComponents_finite_on_compact hD hC hJ hJD
  apply ((hfinite.image (fun n => (K.cutPair n).1)).union
    (hfinite.image (fun n => (K.cutPair n).2))).subset
  intro m hm
  obtain ⟨n, hmn | hmn⟩ := n06_negativePiece_is_cutHalf hN04 hC hm.1
  · left
    refine ⟨n, ?_, hmn.symm⟩
    obtain ⟨p, hp, hpJ⟩ := hm.2
    rw [hmn] at hp
    have hpC := (n06_currentCutHalf_closed_subset_component hN04 hz hs n).1 hp
    exact ⟨p.1, hpC.1, hpJ.1⟩
  · right
    refine ⟨n, ?_, hmn.symm⟩
    obtain ⟨p, hp, hpJ⟩ := hm.2
    rw [hmn] at hp
    have hpC := (n06_currentCutHalf_closed_subset_component hN04 hz hs n).2 hp
    exact ⟨p.1, hpC.1, hpJ.1⟩

end ContinuousFlexibility.Statements
