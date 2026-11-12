import ContinuousFlexibility.Blueprint.CanonicalParts

/-!
# The opposite root is outside the closed physical half

The closed inverse maps a canonical half-strip into its own root circle
and the open negative component. This uses the actual cut curve and
closed inverse identities, without a graph assumption on the cut.
Consequently an actual characteristic approaching an outer endpoint
eventually lies on the correct physical side.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

theorem canonicalCutPair_closed_subset_root_union
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightSide : Bool) :
    physicalPieceClosed S K z (if rightSide then (K.cutPair m).2 else (K.cutPair m).1) ⊆
      ({if rightSide then C.right m else C.left m} ×ˢ (univ : Set ℝ)) ∪
        (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  let i : ℕ := if rightSide then (K.cutPair m).2 else (K.cutPair m).1
  let N : Set PolarPoint := Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
  obtain ⟨_, _, _, _, _, _, hlL, hlR, hrL, hrR⟩ := hcut.1 m
  have hcurrent := hcut.2 z hz hs m
  have hleft : K.left i = 0 := by cases rightSide <;> assumption
  have hright : K.right i = K.cutRadius m := by cases rightSide <;> assumption
  have hzero : K.inverseChart z i '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
      ({if rightSide then C.right m else C.left m} ×ˢ (univ : Set ℝ)) := by
    cases rightSide
    · exact hcurrent.2.2.2.2.1
    · exact hcurrent.2.2.2.2.2
  have htop (θ : ℝ) : K.inverseChart z i (K.cutRadius m, θ) =
      canonicalCutPoint S K z m θ := by
    cases rightSide
    · rfl
    · exact hcurrent.1 θ
  have hopen : physicalPieceOpen S K z i ⊆ N := by
    intro p hp
    have hu : p ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 := by
      cases rightSide
      · exact Or.inl hp
      · exact Or.inr hp
    rw [hcurrent.2.2.2.1] at hu
    exact hu.1
  intro p hp
  let q : PolarPoint := K.chart z i p
  have hclosed := hA.boundary z hz hs i
  have hq : q ∈ canonicalClosed S K i := hclosed.1 hp
  have hqr : q.1 ∈ Icc (0 : ℝ) (K.cutRadius m) := by
    simpa only [hleft, hright] using hq.1
  have hGF : K.inverseChart z i q = p := hclosed.2.2.1 p hp
  rcases lt_or_eq_of_le hqr.1 with hlo | hlo
  · apply Or.inr
    rcases lt_or_eq_of_le hqr.2 with hhi | hhi
    · have hqo : q ∈ canonicalOpen S K i := by
        refine ⟨?_, mem_univ _⟩
        simpa only [hleft, hright] using And.intro hlo hhi
      simpa only [hGF] using hopen ((hA.charts z hz hs i).2.1 hqo)
    · have hpoint : q = (K.cutRadius m, q.2) := Prod.ext hhi rfl
      have hcutq : K.inverseChart z i q ∈ N := by
        rw [hpoint, htop]
        exact hcurrent.2.1 (mem_range_self q.2)
      simpa only [hGF] using hcutq
  · apply Or.inl
    have hroot : K.inverseChart z i q ∈
        ({if rightSide then C.right m else C.left m} ×ˢ (univ : Set ℝ)) := by
      rw [← hzero]
      exact ⟨q, ⟨hlo.symm, mem_univ _⟩, rfl⟩
    simpa only [hGF] using hroot

/-- This excludes the wrong side at every lifted endpoint angle, so that
one-sided characteristic limits use the genuine endpoint chart. -/
theorem canonicalCutPair_opposite_endpoint_not_mem_closed
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightSide : Bool) (θ : ℝ) :
    ((if rightSide then C.left m else C.right m), θ) ∉
      physicalPieceClosed S K z (if rightSide then (K.cutPair m).2 else (K.cutPair m).1) := by
  intro hp
  have hcomponent := (hcut.2 z hz hs m).2.1 (mem_range_self (0 : ℝ))
  have hab : C.left m < C.right m := hcomponent.1.1.trans hcomponent.1.2
  have hne : (if rightSide then C.left m else C.right m) ≠
      (if rightSide then C.right m else C.left m) := by
    cases rightSide
    · exact hab.ne'
    · exact hab.ne
  rcases canonicalCutPair_closed_subset_root_union hA hcut hz hs m rightSide hp with h | h
  · exact hne h.1
  · cases rightSide
    · exact (lt_irrefl _) h.1.2
    · exact (lt_irrefl _) h.1.1

end ContinuousFlexibility.Analysis
