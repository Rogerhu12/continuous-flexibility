import ContinuousFlexibility.Radial.SeedPreparedTail
import ContinuousFlexibility.Radial.SeedConeTailConstruction
import ContinuousFlexibility.Radial.SeedPureTailConstruction
import ContinuousFlexibility.Radial.SeedPureTailCanonical
import ContinuousFlexibility.Radial.SeedGluedPairConstruction
import ContinuousFlexibility.Radial.SeedReturnMargins

/-!
# The actual seed with its selected model and cell transport

The record keeps the data constructed before the existential R08 interface:
one selected Morse family, the actual glued profile and field, and the
coordinate and finite index floor of its final cells.  Its inhabitant is
constructed below from R07.  The original R08 proof projects this same
record rather than choosing a second reference.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

/-- Concrete data retained by the central seed construction. -/
structure SeedReferenceConstruction (q : ℝ) where
  selected : SelectedTailData
  selected_spec : IsSelectedTail selected
  retainedIndex : ℕ
  retainedIndex_ge : selected.chain.index ≤ retainedIndex
  entry_seam : ∀ side : Bool,
    selected.entry side selected.chain.index = morseChainSeam selected.chain side retainedIndex
  entry_core : ∀ side : Bool,
    selected.entry side selected.chain.index ∈ radialCore (selected.family selected.sigma)
  cutoff : SeedCentralCutoff
  glued : SeedGluedPair (selected.family selected.sigma)
    (selected.entry false selected.chain.index) (selected.entry true selected.chain.index)
    (selected.outgoing false 2) (selected.outgoing true 2) cutoff q
  reference : ReferenceData
  left_endpoint : reference.a = glued.radiusL * (selected.family selected.sigma).a
  right_endpoint : reference.b = glued.radiusR * (selected.family selected.sigma).b
  profile : reference.w = glued.profile
  jacobiField : reference.phi = glued.height
  accumulating : IsAccumulatingProfile reference
  construction : RadialConstructionGeometry reference
  indexFloor : ℕ
  indexFloor_pos : 1 ≤ indexFloor
  coordinate : ℝ ≃o ℝ
  cellIndex : reference.cellIndex =
    (fun m => max ((selected.family selected.sigma).cellIndex m) indexFloor)
  cell_pullback : ∀ m, coordinate ⁻¹' (selected.family selected.sigma).cells m ⊆
    reference.cells m
  coordinate_tail : ∀ (side : Bool) (r : ℝ),
    (if side then selected.entry true selected.chain.index ≤ r
     else r ≤ selected.entry false selected.chain.index) →
    coordinate.symm r = (if side then glued.radiusR else glued.radiusL) * r

/-- This is the actual choice made in the seed theorem, with the
quantitative model and cell certificates still attached to its witness. -/
theorem exists_seedReferenceConstruction (hR07 : R07Statement)
    {q : ℝ} (hq : 0 < q) : Nonempty (SeedReferenceConstruction q) := by
  obtain ⟨S, hS, start, hstart, hseams, hentries, hentry⟩ :=
    exists_seedPreparedSelectedTail_with_seams hR07
  let D₀ := S.family S.sigma
  let c := S.entry false S.chain.index
  let d := S.entry true S.chain.index
  have hσ := hS.2.2.1
  have hfamily := hS.2.2.2.1 S.sigma hσ
  have hreal : MorseChainRealization S.chain S.sigma D₀ S.constants := hfamily.1
  have hmass : MorseMassResistanceBounds S.chain S.sigma D₀ S.constants := hfamily.2
  have hD : RadialProfileGeometry D₀ := hreal.geometry
  have hc : c ∈ radialCore D₀ := (hentry false).1
  have hd : d ∈ radialCore D₀ := (hentry true).1
  obtain ⟨CL⟩ := exists_morseSecondMode_coneTail hreal hmass hσ hc
    (hentry false).2.2 (hentry false).2.1
  obtain ⟨CR⟩ := exists_morseSecondMode_coneTail hreal hmass hσ hd
    (hentry true).2.2 (hentry true).2.1
  obtain ⟨PL⟩ := CL.toPureTail hc
  obtain ⟨PR⟩ := CR.toPureTail hd
  obtain ⟨TL, hTL⟩ := PL.toCanonical hD hc
  obtain ⟨TR, hTR⟩ := PR.toCanonical hD hd
  obtain ⟨K⟩ := exists_seedCentralCutoff
  obtain ⟨G⟩ := exists_seedGluedPair hD hc hd TL TR
    (by simpa using hTL) (by simpa using hTR) K hq
  obtain ⟨D, hDa, hDb, hDw, hDphi, hAccum, hConstruction,
    e, N, hN, hindex, hcells, _, hleft, hright⟩ :=
    G.exists_accumulating_reference_with_construction_geometry_transport
      hreal hσ hq hstart (hseams false) (hseams true) hc hd hentries
  exact ⟨{
    selected := S
    selected_spec := hS
    retainedIndex := start
    retainedIndex_ge := hstart
    entry_seam := hseams
    entry_core := fun side => (hentry side).1
    cutoff := K
    glued := G
    reference := D
    left_endpoint := hDa
    right_endpoint := hDb
    profile := hDw
    jacobiField := hDphi
    accumulating := hAccum
    construction := hConstruction
    indexFloor := N
    indexFloor_pos := hN
    coordinate := e
    cellIndex := hindex
    cell_pullback := hcells
    coordinate_tail := by
      intro side r hr
      cases side with
      | false => exact hleft r hr
      | true => exact hright r hr }⟩

namespace SeedReferenceConstruction

variable {q : ℝ} (P : SeedReferenceConstruction q)

theorem realization : MorseChainRealization P.selected.chain P.selected.sigma
    (P.selected.family P.selected.sigma) P.selected.constants :=
  (P.selected_spec.2.2.2.1 P.selected.sigma P.selected_spec.2.2.1).1

/-- Both original model tails are still the actual final profile. -/
theorem tail_profile (side : Bool) {r : ℝ}
    (hr : r ∈ radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index)) :
    P.reference.w ((if side then P.glued.radiusR else P.glued.radiusL) * r) =
      (if side then P.glued.heightR else P.glued.heightL) *
        (if side then P.glued.radiusR else P.glued.radiusL) *
          (P.selected.family P.selected.sigma).w r := by
  rw [P.profile]
  cases side with
  | false => exact (P.glued.left_tail r hr).1
  | true => exact (P.glued.right_tail r hr).1

/-- Every original tail cell is contained in the corresponding actual
final cell, after the exact radius rescaling. -/
theorem tail_cell (side : Bool) (m : ℕ) {r : ℝ}
    (hr : r ∈ radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index))
    (hm : r ∈ (P.selected.family P.selected.sigma).cells m) :
    (if side then P.glued.radiusR else P.glued.radiusL) * r ∈ P.reference.cells m := by
  have he : P.coordinate.symm r =
      (if side then P.glued.radiusR else P.glued.radiusL) * r := by
    apply P.coordinate_tail side r
    cases side with
    | false => exact hr.2.le
    | true => exact hr.1.le
  apply P.cell_pullback m
  change P.coordinate ((if side then P.glued.radiusR else P.glued.radiusL) * r) ∈
    (P.selected.family P.selected.sigma).cells m
  rw [← he, P.coordinate.apply_symm_apply]
  exact hm

end SeedReferenceConstruction

end ContinuousFlexibility.Radial
