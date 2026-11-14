module

public import ContinuousFlexibility.Analysis.N04bActualAtlasCuts
public import ContinuousFlexibility.Analysis.N04bConstructedRootTransmission
public import ContinuousFlexibility.Analysis.N04bActualCharacteristics

/-!
# Transmission for the actual stored negative charts

The two inverse and height germs are supplied by the actual atlas
construction. Their common physical point is the middle of the genuine
travel strip. The constructed root-height identity gives both frozen
transmission conditions for every smooth physical test function.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem n04ActualAtlas_transmission
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u)
    (m : ℕ) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let Wl := canonicalHeight S K z (K.cutPair m).1 u
    let Wr := canonicalHeight S K z (K.cutPair m).2 u
    Wr (K.cutRadius m, θ) = Wl (K.cutRadius m, θ) ∧
      radialPartial Wr (K.cutRadius m, θ) =
        -radialPartial Wl (K.cutRadius m, θ) -
          Wl (K.cutRadius m, θ) / (2 * K.cutRadius m) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let X := n04bActualTravelInverse S C L z m
  have hpos := n04b_actualTravel_positive hN hS hT hfield hz hs m
  have hmid : (C.travel m / 2, θ) ∈
      Ioo (0 : ℝ) (C.travel m) ×ˢ (univ : Set ℝ) :=
    ⟨⟨half_pos hpos, half_lt_self hpos⟩, mem_univ _⟩
  have hX := n04b_actualTravelInverse_spec hN hS hT hfield hz hs m
  have hx : X (C.travel m / 2, θ) ∈
      Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := hX.1 hmid
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hxD : X (C.travel m / 2, θ) ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hx.1.1, hx.1.2.trans (hcontrol.1 m).2.2⟩,
      mem_univ _⟩
  have hXa : DifferentiableAt ℝ X (C.travel m / 2, θ) :=
    (hX.2.2.2.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hmid)).differentiableAt
      (by simp)
  have ha := (hfield.smooth_coefficients z hz hs).1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hxD)
  have hv := (n04b_corrected_characteristics_contDiffAt hN hfield hz hs m hx).2.1
  have hg := n04bActualTypedAtlas_cut_germs hT hS hN hfield e hz hs m θ
  have ht := n04b_canonicalHeight_constructedRoot_cut K z
    (fun side => e.symm (.inl (m, side))) (L.coefficients z)
    (n04bCharacteristicHalfGap (L.coefficients z)) hpos θ hX.2.2.1 hXa
    (ha.differentiableAt (by simp)) (hv.differentiableAt (by simp))
    (hfield.positive_a z hz hs _ hxD)
    (n04b_actualCharacteristic_halfGap_pos hN hfield hz hs m hx)
    hg.1 hg.2 u hu
  simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_cutPair,
    n04bTypedAtlasData_cutRadius] using ht

end ContinuousFlexibility.Analysis
