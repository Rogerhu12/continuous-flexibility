module

public import ContinuousFlexibility.Analysis.CanonicalTravelTransitionAlgebra
public import ContinuousFlexibility.Analysis.N04bActualAtlasGerms
public import ContinuousFlexibility.Analysis.SolveReturnEquations
public import ContinuousFlexibility.Analysis.StateNeighborhood

/-!
# One smooth physical transition for both actual negative halves

The two root reparametrizations cancel against their own inverses. Both
stored reference-to-current maps are therefore the same actual travel
transition on the entire negative component, including the common cut.
All inverse identities and smoothness below come from the constructed
travel chart of the corrected coefficient field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

def n04CoordinatesNegativeTravelTransition (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : PolarPoint :=
  n04bActualTravelInverse S C L z m
    (n04bActualTravelChart S C L (C.referenceState, 0) m p)

def n04CoordinatesNegativeTravelHeightRatio (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : ℝ :=
  let x := n04CoordinatesNegativeTravelTransition S C L z m p
  Real.sqrt (((L.coefficients z).a x * n04bCharacteristicHalfGap (L.coefficients z) x) /
    ((L.coefficients (C.referenceState, 0)).a p *
      n04bCharacteristicHalfGap (L.coefficients (C.referenceState, 0)) p))

section Actual

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ)

include hT hS hN hfield hz hs

theorem n04CoordinatesNegativeTravelTransition_smooth :
    ContDiffOn ℝ ∞ (n04CoordinatesNegativeTravelTransition S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  have hz₀ := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ := hN.1.1.2.2.1.stateSector
  exact (n04b_actualTravelInverse_spec hN hS hT hfield hz hs m).2.2.2.comp
    (n04b_actualTravelChart_smooth hN hS hT hfield hz₀ hs₀ m)
    (n04b_actualTravelChart_bijOn hN hS hT hfield hz₀ hs₀ m).mapsTo

theorem n04CoordinatesNegativeTravelTransition_mapsTo :
    MapsTo (n04CoordinatesNegativeTravelTransition S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  have hz₀ := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ := hN.1.1.2.2.1.stateSector
  intro p hp
  exact (n04b_actualTravelInverse_spec hN hS hT hfield hz hs m).1
    ((n04b_actualTravelChart_bijOn hN hS hT hfield hz₀ hs₀ m).mapsTo hp)

theorem n04CoordinatesNegativeTravelHeightRatio_smooth_pos :
    ContDiffOn ℝ ∞ (n04CoordinatesNegativeTravelHeightRatio S C L z m)
        (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) ∧
      ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
        0 < n04CoordinatesNegativeTravelHeightRatio S C L z m p := by
  have hz₀ := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ := hN.1.1.2.2.1.stateSector
  have hτ := n04CoordinatesNegativeTravelTransition_smooth hT hS hN hfield hz hs m
  have hcore : ∀ y ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      y ∈ annularOpen D := by
    intro y hy
    have hb := hN.1.1.2.2.2.1.1 m
    exact ⟨⟨hb.1.trans hy.1.1, hy.1.2.trans hb.2.2⟩, mem_univ _⟩
  have hpoint (p : PolarPoint) (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
      ContDiffAt ℝ ∞ (n04CoordinatesNegativeTravelHeightRatio S C L z m) p ∧
        0 < n04CoordinatesNegativeTravelHeightRatio S C L z m p := by
    let x := n04CoordinatesNegativeTravelTransition S C L z m p
    have hx : x ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      n04CoordinatesNegativeTravelTransition_mapsTo hT hS hN hfield hz hs m hp
    have hpD := hcore p hp
    have hxD := hcore x hx
    have hτAt := hτ.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
    have ha₀ := (hfield.smooth_coefficients _ hz₀ hs₀).1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpD)
    have ha := (hfield.smooth_coefficients z hz hs).1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hxD)
    have hv₀ := (n04b_corrected_characteristics_contDiffAt hN hfield hz₀ hs₀ m hp).2.1
    have hv := (n04b_corrected_characteristics_contDiffAt hN hfield hz hs m hx).2.1
    have hden := mul_pos (hfield.positive_a _ hz₀ hs₀ p hpD)
      (n04b_actualCharacteristic_halfGap_pos hN hfield hz₀ hs₀ m hp)
    have hnum := mul_pos (hfield.positive_a z hz hs x hxD)
      (n04b_actualCharacteristic_halfGap_pos hN hfield hz hs m hx)
    have hratio := div_pos hnum hden
    refine ⟨?_, Real.sqrt_pos.2 hratio⟩
    have hproduct : ContDiffAt ℝ ∞
        (fun y : PolarPoint =>
          (L.coefficients z).a y * n04bCharacteristicHalfGap (L.coefficients z) y) x :=
      ha.mul hv
    have hratioAt : ContDiffAt ℝ ∞
        (fun y : PolarPoint =>
          ((L.coefficients z).a (n04CoordinatesNegativeTravelTransition S C L z m y) *
            n04bCharacteristicHalfGap (L.coefficients z)
              (n04CoordinatesNegativeTravelTransition S C L z m y)) /
          ((L.coefficients (C.referenceState, 0)).a y *
            n04bCharacteristicHalfGap (L.coefficients (C.referenceState, 0)) y)) p :=
      (ContDiffAt.fun_comp
        (f := n04CoordinatesNegativeTravelTransition S C L z m)
        (g := fun y : PolarPoint =>
          (L.coefficients z).a y * n04bCharacteristicHalfGap (L.coefficients z) y)
        p hproduct hτAt).fun_div (ha₀.mul hv₀) hden.ne'
    exact hratioAt.sqrt hratio.ne'
  exact ⟨fun p hp => (hpoint p hp).1.contDiffWithinAt, fun p hp => (hpoint p hp).2⟩

theorem n04Coordinates_actualAtlas_currentPoint_eq_travel
    (e : ℕ ≃ N04PieceIndex D) (k : ℕ) (side : Bool) (hi : e k = .inl (m, side)) :
    EqOn (canonicalCurrentPoint C (n04bActualTypedAtlas hT hS hN hfield e) z k)
      (n04CoordinatesNegativeTravelTransition S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  have hz₀ := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ := hN.1.1.2.2.1.stateSector
  intro p hp
  have hg₀ := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e hz₀ hs₀ k m side hi hp
  have hF := (n04b_actualTravelChart_bijOn hN hS hT hfield hz₀ hs₀ m).mapsTo hp
  have horient : 0 < n04bTravelOrientation (C.travel m) side
      (n04bActualTravelChart S C L (C.referenceState, 0) m p).1 :=
    n04b_travelOrientation_pos_of_fullStrip side hF.1
  have hpositive : 0 < (n04bRootPhysicalChart
      (n04bActualTravelChart S C L (C.referenceState, 0) m) (C.travel m) side p).1 :=
    n04bRootPhysicalChart_fst_pos horient
  have hG := n04bActualTypedAtlas_negative_inverse_germ
    hT hS hN hfield e hz hs k m side hi
    (q := n04bRootPhysicalChart
      (n04bActualTravelChart S C L (C.referenceState, 0) m) (C.travel m) side p) hpositive
  unfold canonicalCurrentPoint
  rw [hg₀.1.self_of_nhds, hG.self_of_nhds]
  exact n04Coordinates_rootPhysical_transition _ _ _ _ _ horient.le

theorem n04Coordinates_actualAtlas_height_ratio_eq_travel
    (e : ℕ ≃ N04PieceIndex D) (k : ℕ) (side : Bool) (hi : e k = .inl (m, side))
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    (n04bActualTypedAtlas hT hS hN hfield e).height (C.referenceState, 0) k p /
        (n04bActualTypedAtlas hT hS hN hfield e).height z k
          (n04CoordinatesNegativeTravelTransition S C L z m p) =
      n04CoordinatesNegativeTravelHeightRatio S C L z m p := by
  have hz₀ := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ := hN.1.1.2.2.1.stateSector
  let x := n04CoordinatesNegativeTravelTransition S C L z m p
  have hx : x ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    n04CoordinatesNegativeTravelTransition_mapsTo hT hS hN hfield hz hs m hp
  have hF := (n04b_actualTravelChart_bijOn hN hS hT hfield hz₀ hs₀ m).mapsTo hp
  have horient : 0 < n04bTravelOrientation (C.travel m) side
      (n04bActualTravelChart S C L (C.referenceState, 0) m p).1 :=
    n04b_travelOrientation_pos_of_fullStrip side hF.1
  have hsame : n04bActualTravelChart S C L z m x =
      n04bActualTravelChart S C L (C.referenceState, 0) m p :=
    (n04b_actualTravelInverse_spec hN hS hT hfield hz hs m).2.2.1 hF
  have hcore : ∀ y ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      y ∈ annularOpen D := by
    intro y hy
    have hb := hN.1.1.2.2.2.1.1 m
    exact ⟨⟨hb.1.trans hy.1.1, hy.1.2.trans hb.2.2⟩, mem_univ _⟩
  have hg₀ := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e hz₀ hs₀ k m side hi hp
  have hg := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e hz hs k m side hi hx
  change (n04bActualTypedAtlas hT hS hN hfield e).height (C.referenceState, 0) k p /
      (n04bActualTypedAtlas hT hS hN hfield e).height z k x = _
  rw [hg₀.2.self_of_nhds, hg.2.self_of_nhds]
  exact n04Coordinates_rootPhysical_height_ratio _ _ _ _ _ _ _ _ p x hsame
    (hfield.positive_a _ hz₀ hs₀ p (hcore p hp))
    (n04b_actualCharacteristic_halfGap_pos hN hfield hz₀ hs₀ m hp)
    (hfield.positive_a z hz hs x (hcore x hx))
    (n04b_actualCharacteristic_halfGap_pos hN hfield hz hs m hx) horient

end Actual
end ContinuousFlexibility.Analysis
