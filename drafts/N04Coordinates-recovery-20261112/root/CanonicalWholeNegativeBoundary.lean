import ContinuousFlexibility.Analysis.CanonicalWholeNegativeTransport

/-!
# True root germs and physical range of the whole negative transport

The closed component field retains both actual endpoint germs. Its
interior is the genuine travel transition, and its endpoint radius is
fixed. Thus the whole closed component maps into itself, with no value
assigned through a totalized inverse at a turning point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ)

include hT hS hN hfield e

theorem canonicalWholeNegativeTransport_root_germs (side : Bool) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    (canonicalWholeNegativeTransport C K z m =ᶠ[𝓝 (c, θ)]
      canonicalCurrentPoint C K z k) ∧
    (canonicalWholeNegativeHeightRatio C K z m =ᶠ[𝓝 (c, θ)]
      n04CoordinatesCurrentHeightRatio C K z k) := by
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  exact ⟨closedComponentField_root_germ _ hab side θ,
    closedComponentField_root_germ _ hab side θ⟩

include hz hs

theorem canonicalWholeNegativeTransport_root_radial (side : Bool) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let c := if side then C.right m else C.left m
    (canonicalWholeNegativeTransport C K z m (c, θ)).1 = c := by
  have hg := (canonicalWholeNegativeTransport_root_germs hT hS hN hfield e
    (z := z) m side θ).1.eq_of_nhds
  exact (congrArg Prod.fst hg).trans
    ((n04Coordinates_actualAtlas_endpoint_fields hT hS hN hfield e hz hs m side).root_radial θ)

theorem canonicalWholeNegativeTransport_mapsTo_closed :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    MapsTo (canonicalWholeNegativeTransport C K z m)
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  intro p hp
  refine ⟨?_, mem_univ _⟩
  by_cases ha : p.1 = C.left m
  · have he : p = (C.left m, p.2) := Prod.ext ha rfl
    rw [he, canonicalWholeNegativeTransport_root_radial hT hS hN hfield e hz hs m false p.2]
    exact ⟨le_rfl, hab.le⟩
  by_cases hb : p.1 = C.right m
  · have he : p = (C.right m, p.2) := Prod.ext hb rfl
    rw [he, canonicalWholeNegativeTransport_root_radial hT hS hN hfield e hz hs m true p.2]
    exact ⟨hab.le, le_rfl⟩
  have hpin : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm ha), lt_of_le_of_ne hp.1.2 hb⟩, mem_univ _⟩
  have he := (canonicalWholeNegativeTransport_eq_travel hT hS hN hfield e hz hs m).1 p hpin
  rw [he]
  exact Ioo_subset_Icc_self
    (n04CoordinatesNegativeTravelTransition_mapsTo hT hS hN hfield hz hs m hpin).1

end ContinuousFlexibility.Analysis
