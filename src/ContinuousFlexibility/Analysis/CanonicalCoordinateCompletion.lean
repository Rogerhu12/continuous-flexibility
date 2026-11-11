import ContinuousFlexibility.Analysis.CanonicalJetNormalization
import ContinuousFlexibility.Analysis.CanonicalSourceConversion

/-!
# The precise remaining estimate in the canonical coordinate stage

The source-pairing identity follows from the qualitative coordinate geometry.
Consequently the full frozen `N04Properties` is equivalent to `N04PartA`,
`N04PartB`, and the actual uniform jet bound.  The equivalence retains every
quantifier and the same base, derivative loss, and neighborhood radius.

No existence of quantitatively controlled coordinates is asserted here.
The last theorem assembles such coordinates once their sector estimate has
been proved, using normalization only on fields that the identities do not use.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- The source formula is a consequence of the coordinate hypotheses, so
the exact additional obligation is the frozen uniform jet bound. -/
theorem n04Properties_iff_parts_and_jetBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ} :
    N04Properties D T S C L K base loss ε ↔
      N04PartA D S C K base ε ∧ N04PartB S C L K base ε ∧
        CanonicalJetBounds T S C K base loss ε := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, _⟩ := h
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩,
      ⟨h12, h13, h14, h15, h16⟩, h17⟩
  · rintro ⟨hA, hB, hbound⟩
    have hgeometry := hA
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hA
    obtain ⟨h12, h13, h14, h15, h16⟩ := hB
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, hbound, ?_⟩
    intro z hz hs m u f _ _ _ _ _ _
    exact canonicalSource_pairing_of_partA hgeometry hz hs m u f

/-- Assemble the exact canonical properties from their qualitative pieces
and an independently proved uniform estimate. -/
theorem n04Properties_of_parts_of_jetBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hbound : CanonicalJetBounds T S C K base loss ε) :
    N04Properties D T S C L K base loss ε :=
  n04Properties_iff_parts_and_jetBounds.mpr ⟨hA, hB, hbound⟩

/-- A genuine sector estimate completes the same data after normalizing
only unused potentials and divided coefficients. -/
theorem n04Properties_normalized_of_sector_jetBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hbound : SectorCanonicalJetBounds T S C K base loss ε) :
    N04Properties D T S C L (normalizedCanonicalData S K) base loss ε :=
  n04Properties_of_parts_of_jetBounds (n04PartA_normalizedCanonicalData hA)
    (n04PartB_normalizedCanonicalData hB)
    (canonicalJetBounds_normalized_of_sector_of_material hT hD hbound)

end ContinuousFlexibility.Analysis
