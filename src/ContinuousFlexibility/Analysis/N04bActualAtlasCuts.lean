module

public import ContinuousFlexibility.Analysis.N04bActualAtlasGerms

/-!
# The actual cut geometry of the final atlas

The closed travel inverse identifies both root circles and the shared
moving middle curve. The same equivalence indexes the two stored sides.
The resulting concrete atlas satisfies all of Part A and the complete
current cut geometry, using only the cumulative field construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)

theorem n04bActualTypedAtlas_currentCutPair
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    CanonicalCurrentCutPair S C (n04bActualTypedAtlas hT hS hN hfield e) z m := by
  have hpos := n04b_actualTravel_positive hN hS hT hfield hz hs m
  have hClosed := n04b_actualClosedTravelInverse_spec hN hS hT hfield hz hs m
  have hOpen := n04b_actualTravelInverse_spec hN hS hT hfield hz hs m
  refine n04b_currentCutPair_of_constructedRoot C
    (n04bActualTypedAtlas hT hS hN hfield e) z m
    (fun side => e.symm (.inl (m, side)))
    (X := n04bActualClosedTravelInverse S C L z m) hpos
    (n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m) ?_ ?_
    (n04b_actualClosedTravelInverse_endpoint_images hN hS hT hfield hz hs m)
    rfl rfl ?_ ?_
  · intro q hq
    rw [hClosed.2.2.2.2 hq]
    exact hOpen.1 hq
  · intro q hq
    exact hClosed.2.2.1 ⟨⟨hq.1.1.le, hq.1.2.le⟩, mem_univ _⟩
  · intro side
    simp only [n04bActualTypedAtlas, n04bTypedAtlasData_physicalPieceOpen,
      Equiv.apply_symm_apply, n04bTypedPhysicalDomain]
  · intro side
    exact n04bActualTypedAtlas_negative_closed_inverse hT hS hN hfield e hz hs
      (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)

theorem n04bActualTypedAtlas_cutGeometry :
    CanonicalCutGeometry S C (n04bActualTypedAtlas hT hS hN hfield e) base ε := by
  constructor
  · exact n04bTypedAtlasData_referenceCutPairs e
      (n04bActualNegativeChart hT hS hN hfield)
      (n04bActualNegativeHeight hT hS hN hfield)
      (n04bActualNegativeInverse hT hS hN hfield)
      (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1
      (n04bActualReferenceCut hN)
  · intro z hz hs m
    exact n04bActualTypedAtlas_currentCutPair hT hS hN hfield e hz hs m

/-- The stored trace is the actual physical middle-travel curve, with
the smooth open travel inverse as its literal formula. -/
theorem n04bActualTypedAtlas_cutPoint
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    canonicalCutPoint S (n04bActualTypedAtlas hT hS hN hfield e) z m =
      fun θ => n04bActualTravelInverse S C L z m (C.travel m / 2, θ) := by
  have hpos := n04b_actualTravel_positive hN hS hT hfield hz hs m
  have hClosed := n04b_actualClosedTravelInverse_spec hN hS hT hfield hz hs m
  have htrace := n04b_canonicalCutPoint_of_constructedRoot
    (n04bActualTypedAtlas hT hS hN hfield e) z m
    (fun side => e.symm (.inl (m, side)))
    (n04bActualClosedTravelInverse S C L z m) hpos rfl rfl
    (fun side => n04bActualTypedAtlas_negative_closed_inverse hT hS hN hfield e hz hs
      (e.symm (.inl (m, side))) m side (e.apply_symm_apply _))
  rw [htrace]
  funext θ
  exact hClosed.2.2.2.2
    ⟨⟨half_pos hpos, half_lt_self hpos⟩, mem_univ _⟩

/-- One actual enumeration yields the complete geometric construction.
No canonical map or geometric certificate is an input to this theorem. -/
theorem n04b_exists_actual_typed_atlas :
    ∃ e : ℕ ≃ N04PieceIndex D,
      CanonicalGeometry D S C (n04bActualTypedAtlas hT hS hN hfield e) base ε ∧
        CanonicalCutGeometry S C (n04bActualTypedAtlas hT hS hN hfield e) base ε := by
  have hD := n04b_profileGeometry_of_through03 hN
  obtain ⟨e⟩ := n04b_exists_piece_enumeration
    (hD.2.2.1.1.continuous_deriv (by simp))
  exact ⟨e, n04b_actualTypedAtlas_partA hT hS hN hfield e,
    n04bActualTypedAtlas_cutGeometry hT hS hN hfield e⟩

end ContinuousFlexibility.Analysis
