import ContinuousFlexibility.Analysis.N04bActualAtlasGeometry

/-!
# Actual formula germs retained by the final atlas

These are proved identities of the concrete record, not additional
hypotheses on an arbitrary atlas. They retain the physical chart and
height germs on the entire negative component, the genuine closed
inverse, and both positive-radius cut germs needed by transmission.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hT hS hN hfield hz hs

theorem n04bActualTypedAtlas_negative_component_germs
    (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side))
    {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    K.chart z k =ᶠ[𝓝 p]
        n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side ∧
      K.height z k =ᶠ[𝓝 p]
        n04bRootPhysicalHeight (L.coefficients z)
          (n04bCharacteristicHalfGap (L.coefficients z))
          (n04bActualTravelChart S C L z m) (C.travel m) side := by
  have H := n04bActualNegativeFunctions_spec hT hS hN hfield hz hs m side
  simpa only [n04bActualTypedAtlas, n04bTypedAtlasData_chart,
    n04bTypedAtlasData_height, hi, n04bTypedAtlasChart, n04bTypedAtlasHeight] using
    And.intro (H.component_chart_germ hp) (H.component_height_germ hp)

theorem n04bActualTypedAtlas_negative_closed_inverse
    (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side)) :
    EqOn ((n04bActualTypedAtlas hT hS hN hfield e).inverseChart z k)
      (n04bRootPhysicalInverse (n04bActualClosedTravelInverse S C L z m) (C.travel m) side)
      (Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ)) := by
  have H := n04bActualNegativeFunctions_spec hT hS hN hfield hz hs m side
  simpa only [n04bActualTypedAtlas, n04bTypedAtlasData_inverseChart,
    hi, n04bTypedAtlasInverse] using H.closed_inverse_eq

theorem n04bActualTypedAtlas_negative_inverse_germ
    (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side))
    {q : PolarPoint} (hq : 0 < q.1) :
    (n04bActualTypedAtlas hT hS hN hfield e).inverseChart z k =ᶠ[𝓝 q]
      n04bRootPhysicalInverse (n04bActualTravelInverse S C L z m) (C.travel m) side := by
  have H := n04bActualNegativeFunctions_spec hT hS hN hfield hz hs m side
  simpa only [n04bActualTypedAtlas, n04bTypedAtlasData_inverseChart,
    hi, n04bTypedAtlasInverse] using H.inverse_physical_germ q hq

/-- Both actual atlas sides have exactly the germs consumed by the
proved root-height transmission formula at the common positive radius. -/
theorem n04bActualTypedAtlas_cut_germs (m : ℕ) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let piece := fun side : Bool => e.symm (.inl (m, side))
    (∀ side : Bool,
      K.inverseChart z (piece side) =ᶠ[𝓝 (n04bRootCutRadius (C.travel m), θ)]
        n04bRootPhysicalInverse (n04bActualTravelInverse S C L z m)
          (C.travel m) side) ∧
      (∀ side : Bool,
        K.height z (piece side) =ᶠ[𝓝 (n04bActualTravelInverse S C L z m (C.travel m / 2, θ))]
          n04bRootPhysicalHeight (L.coefficients z)
            (n04bCharacteristicHalfGap (L.coefficients z))
            (n04bActualTravelChart S C L z m) (C.travel m) side) := by
  have hpos := n04b_actualTravel_positive hN hS hT hfield hz hs m
  have hmid : (C.travel m / 2, θ) ∈
      Ioo (0 : ℝ) (C.travel m) ×ˢ (univ : Set ℝ) :=
    ⟨⟨half_pos hpos, half_lt_self hpos⟩, mem_univ _⟩
  have hx := (n04b_actualTravelInverse_spec hN hS hT hfield hz hs m).1 hmid
  constructor
  · intro side
    exact n04bActualTypedAtlas_negative_inverse_germ hT hS hN hfield e hz hs
      (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
      (n04bRootCutRadius_pos hpos)
  · intro side
    exact (n04bActualTypedAtlas_negative_component_germs hT hS hN hfield e hz hs
      (e.symm (.inl (m, side))) m side (e.apply_symm_apply _) hx).2

end ContinuousFlexibility.Analysis
