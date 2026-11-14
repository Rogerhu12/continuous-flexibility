module

public import ContinuousFlexibility.Analysis.N04bActualTravelChart
public import ContinuousFlexibility.Analysis.N04bConstructedRootTransmission

/-!
# Transmission at the actual moving middle curve

The actual travel inverse and raw corrected-field regularity supply all
differentiability and positivity used in the root-height calculation.
The remaining inputs identify the literal atlas maps with their already
constructed formulas near the positive cut radius.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n04b_actualRoot_cut_transmission
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (K : CanonicalData S) (piece : Bool → ℕ) (θ : ℝ)
    (hInverse : ∀ side : Bool,
      K.inverseChart z (piece side) =ᶠ[𝓝 (n04bRootCutRadius (C.travel m), θ)]
        n04bRootPhysicalInverse (n04bActualTravelInverse S C L z m) (C.travel m) side)
    (hHeight : ∀ side : Bool,
      K.height z (piece side) =ᶠ[𝓝 (n04bActualTravelInverse S C L z m (C.travel m / 2, θ))]
        n04bRootPhysicalHeight (L.coefficients z)
          (n04bCharacteristicHalfGap (L.coefficients z))
          (n04bActualTravelChart S C L z m) (C.travel m) side)
    (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u) :
    canonicalHeight S K z (piece true) u (n04bRootCutRadius (C.travel m), θ) =
        canonicalHeight S K z (piece false) u (n04bRootCutRadius (C.travel m), θ) ∧
      radialPartial (canonicalHeight S K z (piece true) u)
          (n04bRootCutRadius (C.travel m), θ) =
        -radialPartial (canonicalHeight S K z (piece false) u)
            (n04bRootCutRadius (C.travel m), θ) -
          canonicalHeight S K z (piece false) u (n04bRootCutRadius (C.travel m), θ) /
            (2 * n04bRootCutRadius (C.travel m)) := by
  have htime : 0 < C.travel m := n04b_actualTravel_positive h03 hS hT hfield hz hs m
  have hmiddle : (C.travel m / 2, θ) ∈
      Ioo (0 : ℝ) (C.travel m) ×ˢ (univ : Set ℝ) :=
    ⟨⟨half_pos htime, half_lt_self htime⟩, mem_univ _⟩
  have hspec := n04b_actualTravelInverse_spec h03 hS hT hfield hz hs m
  have hx := hspec.1 hmiddle
  have hX : DifferentiableAt ℝ (n04bActualTravelInverse S C L z m)
      (C.travel m / 2, θ) :=
    (hspec.2.2.2.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hmiddle)).differentiableAt (by simp)
  have hcontrol : controlGeometryConditions D S C := h03.1.1.2.2.2.1
  have hxD : n04bActualTravelInverse S C L z m (C.travel m / 2, θ) ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hx.1.1, hx.1.2.trans (hcontrol.1 m).2.2⟩,
      mem_univ _⟩
  have ha := ((hfield.smooth_coefficients z hz hs).1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hxD)).differentiableAt (by simp)
  have hv := (n04b_corrected_characteristics_contDiffAt h03 hfield hz hs m hx).2.1
  apply n04b_canonicalHeight_constructedRoot_cut K z piece
    (L.coefficients z) (n04bCharacteristicHalfGap (L.coefficients z))
    htime θ ?_ hX ha (hv.differentiableAt (by simp))
    (hfield.positive_a z hz hs _ hxD)
    (n04b_actualCharacteristic_halfGap_pos h03 hfield hz hs m hx)
    hInverse hHeight u hu
  intro q hq
  exact hspec.2.2.1 hq

end ContinuousFlexibility.Analysis
