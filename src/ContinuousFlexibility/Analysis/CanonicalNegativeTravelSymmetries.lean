import ContinuousFlexibility.Analysis.CanonicalNegativeTravelTransition

/-!
# Symmetries of the actual common negative transport

The reference and current travel charts have the same angular period and
reflection. Their genuine inverse therefore transports these symmetries
to the whole negative component. The height ratio uses the actual
coefficient amplitude, whose periodicity and parity are retained by N03.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ)

include hT hS hN hfield hz hs

theorem n04CoordinatesNegativeTravelTransition_symmetries
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    n04CoordinatesNegativeTravelTransition S C L z m (p + (0, Real.pi)) =
        n04CoordinatesNegativeTravelTransition S C L z m p + (0, Real.pi) ∧
      n04CoordinatesNegativeTravelTransition S C L z m (p.1, -p.2) =
        ((n04CoordinatesNegativeTravelTransition S C L z m p).1,
          -(n04CoordinatesNegativeTravelTransition S C L z m p).2) := by
  have hz₀ := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ := hN.1.1.2.2.1.stateSector
  have hF := (n04b_actualTravelChart_bijOn hN hS hT hfield hz₀ hs₀ m).mapsTo hp
  have hX := n04b_actualTravelInverse_symmetries hN hS hT hfield hz hs m hF
  constructor
  · have hperiod : n04bActualTravelChart S C L (C.referenceState, 0) m
        (p + (0, Real.pi)) =
          n04bActualTravelChart S C L (C.referenceState, 0) m p + (0, Real.pi) := by
      simpa only [Prod.add_def, add_zero, Prod.eta] using
        n04b_actualTravelChart_period_add hN hS hT hfield hz₀ hs₀ m
          ⟨hp.1.1.le, hp.1.2.le⟩ p.2
    unfold n04CoordinatesNegativeTravelTransition
    rw [hperiod]
    exact hX.1
  · unfold n04CoordinatesNegativeTravelTransition
    rw [n04b_actualTravelChart_reflection m p]
    exact hX.2

theorem n04CoordinatesNegativeTravelHeightRatio_symmetries
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    n04CoordinatesNegativeTravelHeightRatio S C L z m (p + (0, Real.pi)) =
        n04CoordinatesNegativeTravelHeightRatio S C L z m p ∧
      n04CoordinatesNegativeTravelHeightRatio S C L z m (p.1, -p.2) =
        n04CoordinatesNegativeTravelHeightRatio S C L z m p := by
  have hz₀ := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ := hN.1.1.2.2.1.stateSector
  have hτ := n04CoordinatesNegativeTravelTransition_symmetries hT hS hN hfield hz hs m hp
  have hcore : ∀ y ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      y ∈ annularOpen D := by
    intro y hy
    have hb := hN.1.1.2.2.2.1.1 m
    exact ⟨⟨hb.1.trans hy.1.1, hy.1.2.trans hb.2.2⟩, mem_univ _⟩
  have hx := hcore _ (n04CoordinatesNegativeTravelTransition_mapsTo
    hT hS hN hfield hz hs m hp)
  have hperiod (w : AnnularState S × ℝ) (hw : w ∈ stateNeighborhood S C base ε)
      (hsw : stateSector S w.1) (y : PolarPoint) (hy : y ∈ annularOpen D) :
      (L.coefficients w).a (y + (0, Real.pi)) *
          n04bCharacteristicHalfGap (L.coefficients w) (y + (0, Real.pi)) =
        (L.coefficients w).a y * n04bCharacteristicHalfGap (L.coefficients w) y := by
    have h := hfield.periodic_coefficients w hw hsw y.1 hy.1
    have hv := (n04b_characteristic_periodic (L.coefficients w) y.1 Real.pi
      h.1 h.2.1 h.2.2).2 y.2
    have ha := h.1 y.2
    simpa only [Prod.add_def, add_zero, Prod.eta] using congrArg₂ (· * ·) ha hv
  have hreflect (w : AnnularState S × ℝ) (hw : w ∈ stateNeighborhood S C base ε)
      (hsw : stateSector S w.1) (y : PolarPoint) :
      (L.coefficients w).a (y.1, -y.2) *
          n04bCharacteristicHalfGap (L.coefficients w) (y.1, -y.2) =
        (L.coefficients w).a y * n04bCharacteristicHalfGap (L.coefficients w) y := by
    rw [(hN.2.2.2.2.1 w hw hsw y.1 y.2).1,
      (n04b_actualCharacteristic_reflection hN hw hsw y).2]
  constructor
  · dsimp only [n04CoordinatesNegativeTravelHeightRatio]
    rw [hτ.1,
      hperiod z hz hs (n04CoordinatesNegativeTravelTransition S C L z m p) hx,
      hperiod _ hz₀ hs₀ p (hcore p hp)]
  · dsimp only [n04CoordinatesNegativeTravelHeightRatio]
    rw [hτ.2,
      hreflect z hz hs (n04CoordinatesNegativeTravelTransition S C L z m p),
      hreflect _ hz₀ hs₀ p]

end ContinuousFlexibility.Analysis
