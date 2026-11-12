import ContinuousFlexibility.Blueprint.CanonicalParts
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Genuine open pieces cannot contain the cut

An almost-everywhere unique partition by open sets is everywhere disjoint.
Each actual cut point lies in both closed halves. Any open piece containing
that point would therefore meet both halves, contradicting disjointness.
This recovers the negative paired pieces without assuming that the cut is
a graph or that its image has already been proved to have measure zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

theorem open_pieces_pairwise_disjoint_of_ae_unique
    {U E : Set PolarPoint} {Ω : ℕ → Set PolarPoint}
    (hopen : ∀ i, IsOpen (Ω i)) (hsub : ∀ i, Ω i ⊆ U)
    (hE : volume E = 0) (hcover : ∀ p ∈ U \ E, ∃! i, p ∈ Ω i) :
    Pairwise (fun i j => Disjoint (Ω i) (Ω j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hpi hpj
  have hpos : 0 < volume (Ω i ∩ Ω j) :=
    ((hopen i).inter (hopen j)).measure_pos volume ⟨p, hpi, hpj⟩
  have hsubset : Ω i ∩ Ω j ⊆ E := by
    intro q hq
    by_contra hqE
    obtain ⟨k, _, hu⟩ := hcover q ⟨hsub i hq.1, hqE⟩
    exact hij ((hu i hq.1).trans (hu j hq.2).symm)
  have hmeasure : volume (Ω i ∩ Ω j) ≤ volume E := measure_mono hsubset
  rw [hE] at hmeasure
  exact (not_le_of_gt hpos) hmeasure

theorem canonicalPhysicalPieces_pairwise_disjoint
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    Pairwise (fun i j => Disjoint (physicalPieceOpen S K z i) (physicalPieceOpen S K z j)) := by
  obtain ⟨E, hE, hcover⟩ := hA.partition z hz hs
  exact open_pieces_pairwise_disjoint_of_ae_unique
    (fun i => (hA.domains z hz hs i).1)
    (fun i => (hA.domains z hz hs i).2.2.1) hE hcover

theorem canonicalCutPair_indices_ne
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) : (K.cutPair m).1 ≠ (K.cutPair m).2 := by
  intro he
  obtain ⟨p, hp⟩ := (hA.domains z hz hs (K.cutPair m).1).2.1
  exact Set.disjoint_left.mp (hcut.2 z hz hs m).2.2.1 hp (by simpa only [he] using hp)

theorem canonicalCutPoint_mem_both_closed
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    canonicalCutPoint S K z m θ ∈ physicalPieceClosed S K z (K.cutPair m).1 ∧
      canonicalCutPoint S K z m θ ∈ physicalPieceClosed S K z (K.cutPair m).2 := by
  obtain ⟨_, _, _, _, _, hρ, hlL, hlR, hrL, hrR⟩ := hcut.1 m
  have hqL : (K.cutRadius m, θ) ∈ canonicalClosed S K (K.cutPair m).1 := by
    refine ⟨?_, mem_univ _⟩
    rw [hlL, hrL]
    exact ⟨hρ.le, le_rfl⟩
  have hqR : (K.cutRadius m, θ) ∈ canonicalClosed S K (K.cutPair m).2 := by
    refine ⟨?_, mem_univ _⟩
    rw [hlR, hrR]
    exact ⟨hρ.le, le_rfl⟩
  refine ⟨(hA.boundary z hz hs (K.cutPair m).1).2.1 hqL, ?_⟩
  have hr := (hA.boundary z hz hs (K.cutPair m).2).2.1 hqR
  rwa [(hcut.2 z hz hs m).1 θ] at hr

theorem canonicalCutPoint_not_mem_any_open
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) (i : ℕ) :
    canonicalCutPoint S K z m θ ∉ physicalPieceOpen S K z i := by
  intro hp
  have hclosed := canonicalCutPoint_mem_both_closed hA hcut hz hs m θ
  have hdis := canonicalPhysicalPieces_pairwise_disjoint hA hz hs
  have hnear := (hA.domains z hz hs i).1.mem_nhds hp
  obtain ⟨x, hxi, hxL⟩ := mem_closure_iff_nhds.mp hclosed.1 _ hnear
  obtain ⟨y, hyi, hyR⟩ := mem_closure_iff_nhds.mp hclosed.2 _ hnear
  have hiL : i = (K.cutPair m).1 := by
    by_contra hne
    exact Set.disjoint_left.mp (hdis hne) hxi hxL
  have hiR : i = (K.cutPair m).2 := by
    by_contra hne
    exact Set.disjoint_left.mp (hdis hne) hyi hyR
  exact canonicalCutPair_indices_ne hA hcut hz hs m (hiL.symm.trans hiR)

theorem canonicalCutPair_index_of_open_mem_component
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {i : ℕ} {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K z i) (hN : p.1 ∈ Ioo (C.left m) (C.right m)) :
    i = (K.cutPair m).1 ∨ i = (K.cutPair m).2 := by
  have hnot : p ∉ Set.range (canonicalCutPoint S K z m) := by
    rintro ⟨θ, hθ⟩
    exact canonicalCutPoint_not_mem_any_open hA hcut hz hs m θ i
      (by simpa only [hθ] using hp)
  have hmem : p ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
      physicalPieceOpen S K z (K.cutPair m).2 := by
    rw [(hcut.2 z hz hs m).2.2.2.1]
    exact ⟨⟨hN, mem_univ _⟩, hnot⟩
  have hdis := canonicalPhysicalPieces_pairwise_disjoint hA hz hs
  rcases hmem with hl | hr
  · apply Or.inl
    by_contra hne
    exact Set.disjoint_left.mp (hdis hne) hp hl
  · apply Or.inr
    by_contra hne
    exact Set.disjoint_left.mp (hdis hne) hp hr

/-- Every negative index is one of the actual paired half-indices. This
is a consequence of the partition, not an extra surjectivity assumption. -/
theorem canonicalNegativePiece_is_paired
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    (hC : controlGeometryConditions D S C)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : ℕ) (hi : K.positive i = false) :
    ∃ m : ℕ, i = (K.cutPair m).1 ∨ i = (K.cutPair m).2 := by
  obtain ⟨p, hp⟩ := (hA.domains z hz hs i).2.1
  have hr : p.1 ∈ Ioo D.a D.b := ((hA.domains z hz hs i).2.2.1 hp).1
  have hn := (hA.domains z hz hs i).2.2.2.2.2.2.2 p hp hi
  obtain ⟨m, hm⟩ := hC.2.2.2.2.1 p.1 hr hn
  exact ⟨m, canonicalCutPair_index_of_open_mem_component hA hcut hz hs m hp hm⟩

end ContinuousFlexibility.Analysis
