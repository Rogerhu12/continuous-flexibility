import ContinuousFlexibility.Radial.R11aRetainedFamily
import ContinuousFlexibility.Analysis.N05SeedOpticalLower

/-!
# The optical lower certificate on the same completed retained reference

Integration target: the proved R11a tree at
`bfa87806ee8e2ca5794e919764f37c8424b47b30`, together with the companion
`drafts/N05SeedReferenceRetention.patch`. The patch weakens only the local
construction record's exact `cells` equality to `cell_pullback`, uses the
proved `exists_accumulating_reference_with_construction_geometry_transport`
constructor, updates `tail_cell`, and removes the unused reverse `cell_point`
lemma. It is not applied by this draft. The eight optical modules, and the
negative-component enumeration, need no proof or statement changes.

The retained pair is reinterpreted by its actual `toEntryPair`. This changes
only the entrance bookkeeping: profile, height and both dilation radii remain
the same. The constructed record's `reference` is definitionally the input
`Γ.reference`. No new physical profile, partition, or inverse is selected.

The proof uses only the closed R11a coordinate certificate, the actual
profile/height identities and construction geometry. The selected first band
is `metadata.first_two` in the retained assembly, and `metadata.selected`
supplies its selected-tail condition. No open Blueprint result is applied.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements

/-- Every field of the weaker seed record is supplied by the original
retained pair and its own reference. -/
theorem exists_n05_seedReferenceConstruction_of_retained
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {Γ : ConnectedReferenceGeometry}
    (hw : Γ.reference.w = P.pair.profile)
    (hphi : Γ.reference.phi = P.pair.height)
    (hacc : IsAccumulatingProfile Γ.reference)
    (hconstruction : RadialConstructionGeometry Γ.reference)
    (hcoordinates : R11aRetainedCoordinates P Γ) :
    ∃ Q : SeedReferenceConstruction q,
      Q.reference = Γ.reference ∧ Q.selected = S ∧
      Q.retainedIndex = S.chain.index ∧
      Q.glued.profile = P.pair.profile ∧ Q.glued.height = P.pair.height := by
  obtain ⟨e, N, hN, hraw, hindex, hcells, _, hleft, hright, _, ha, hb⟩ := hcoordinates
  have hseam (side : Bool) :
      S.entry side S.chain.index = morseChainSeam S.chain side S.chain.index := by
    simpa only [morseChainSeam] using
      (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.2.1
  have hentry (side : Bool) :
      S.entry side S.chain.index ∈ radialCore (S.family S.sigma) :=
    (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband).2.1
  let Q : SeedReferenceConstruction q := {
    selected := S
    selected_spec := hS
    retainedIndex := S.chain.index
    retainedIndex_ge := le_rfl
    entry_seam := hseam
    entry_core := hentry
    cutoff := K
    glued := P.toEntryPair hS hband
    reference := Γ.reference
    left_endpoint := ha
    right_endpoint := hb
    profile := by simpa only [SeedRetainedPair.toEntryPair_profile] using hw
    jacobiField := by simpa only [SeedRetainedPair.toEntryPair_height] using hphi
    accumulating := hacc
    construction := hconstruction
    indexFloor := N
    indexFloor_pos := hN
    coordinate := e
    cellIndex := by simpa only [hraw] using hindex
    cell_pullback := hcells
    coordinate_tail := by
      intro side r hr
      cases side with
      | false => exact hleft r hr
      | true => exact hright r hr }
  exact ⟨Q, rfl, rfl, rfl, rfl, rfl⟩

end ContinuousFlexibility.Radial

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Radial

/-- The actual completed retained reference itself has the optical lower
bound on every control component and every one of its actual carriers. -/
theorem n05_actualCarrierOpticalLower_of_retained_coordinates
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry}
    (hw : Γ.reference.w = P.pair.profile)
    (hphi : Γ.reference.phi = P.pair.height)
    (hD : IsRadialReference Γ.reference)
    (hconstruction : RadialConstructionGeometry Γ.reference)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {X : PhysicalSpacesData} {C : NonlinearGeometryData X}
    (hC : controlGeometryConditions Γ.reference X C) :
    N05ActualCarrierOpticalLower Γ.reference C := by
  obtain ⟨Q, hQ, _, _, _, _⟩ :=
    exists_n05_seedReferenceConstruction_of_retained P hS hband
      hw hphi hD.1 hconstruction hcoordinates
  have hCQ : controlGeometryConditions Q.reference X C := by
    simpa only [hQ] using hC
  simpa only [hQ] using n05_actualCarrierOpticalLower_of_seed Q hq hCQ

end ContinuousFlexibility.Statements
