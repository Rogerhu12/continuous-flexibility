import ContinuousFlexibility.Analysis.N04bActualRootCoordinates
import ContinuousFlexibility.Analysis.N04bLeftRootFlowGeometry
import ContinuousFlexibility.Analysis.N04bRightRootFlowGeometry

/-!
# Root-coordinate functions constructed from the actual N03 data

At the left root the angular normalization is the actual state left
chart. At the right root it is the actual N01 right chart and the stored
flow is normalized by its genuine terminal inverse. Both labels are
smooth increasing odd circle lifts. The physical root equations then
construct one smooth G for both characteristics at each endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual left-root coordinate function, with both characteristic
footpoints and all boundary coefficient data proved from Through03. -/
theorem n04b_exists_left_physical_root_coordinate_with_halfGap
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ),
      0 < ρ ∧ C.left m + ρ < C.right m ∧
      N04bRootCoordinateProperties d c₀ (stateLeftChart S z.1 m)
        (fun θ x => L.minusFlow z m (C.left m + x) θ) ρ (-1) G ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        Real.sqrt x * c₀ (x, θ) =
          n04bCharacteristicHalfGap (L.coefficients z) (C.left m + x, θ)) := by
  obtain ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos,
      hi, hcont, hflow, hgap⟩ :=
    n04b_exists_left_root_symmetric_flow_equations_with_halfGap hT hS h03 hL hz hs m
  have hleft := h03.1.1.2.2.2.2.2.2.2.1 z hz hs m
  have hhL : ContDiff ℝ ∞ (stateLeftChart S z.1 m) :=
    stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))
  have hLpos : ∀ θ, 0 < deriv (stateLeftChart S z.1 m) θ :=
    fun θ => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hleft θ).1
  obtain ⟨G, hG⟩ := n04b_exists_actual_root_coordinate hρ hd hc hdp hcp
    hdodd hceven (fun θ => hcpos (0, θ)) hi hcont hflow hhL hLpos
    (fun θ => (hleft θ).2.2.1) (fun θ => (hleft θ).2.2.2)
  exact ⟨ρ, d, c₀, G, hρ, hsmall, hG, hgap⟩

/-- Projection retaining the established root-coordinate interface. -/
theorem n04b_exists_left_physical_root_coordinate
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ),
      0 < ρ ∧ C.left m + ρ < C.right m ∧
      N04bRootCoordinateProperties d c₀ (stateLeftChart S z.1 m)
        (fun θ x => L.minusFlow z m (C.left m + x) θ) ρ (-1) G := by
  obtain ⟨ρ, d, c₀, G, hρ, hsmall, hG, _⟩ :=
    n04b_exists_left_physical_root_coordinate_with_halfGap hT hS h03 hL hz hs m
  exact ⟨ρ, d, c₀, G, hρ, hsmall, hG⟩

/-- The actual right-root coordinate uses the existing right angular
chart and the true terminal inverse, with no assumed endpoint chart. -/
theorem n04b_exists_right_physical_root_coordinate_with_halfGap
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ),
      0 < ρ ∧ C.left m < C.right m - ρ ∧
      N04bRootCoordinateProperties d c₀ (rightChartCandidate S C z m)
        (n04bRightRootFlow C L z m) ρ 1 G ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        Real.sqrt x * c₀ (x, θ) =
          n04bCharacteristicHalfGap (L.coefficients z) (C.right m - x, θ)) := by
  obtain ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos,
      hi, hcont, hflow, hgap⟩ :=
    n04b_exists_right_root_symmetric_flow_equations_with_halfGap hT hS h03 hL hz hs m
  have hN := h03.1.1
  have hhR : ContDiff ℝ ∞ (rightChartCandidate S C z m) :=
    hN.rightChartCandidate_contDiff hS hT hz hs m
  have hRpos : ∀ θ, 0 < deriv (rightChartCandidate S C z m) θ :=
    N01Properties.rightChart_deriv_pos S C z m hN hz hs
  have hRodd : ∀ θ, rightChartCandidate S C z m (-θ) =
      -rightChartCandidate S C z m θ := by
    intro θ
    simp only [rightChartCandidate, oddPart, neg_neg]
    ring
  obtain ⟨G, hG⟩ := n04b_exists_actual_root_coordinate hρ hd hc hdp hcp
    hdodd hceven (fun θ => hcpos (0, θ)) hi hcont hflow hhR hRpos
    (hN.rightChartCandidate_add_period hz hs m) hRodd
  exact ⟨ρ, d, c₀, G, hρ, hsmall, hG, hgap⟩

/-- Projection retaining the established root-coordinate interface. -/
theorem n04b_exists_right_physical_root_coordinate
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ),
      0 < ρ ∧ C.left m < C.right m - ρ ∧
      N04bRootCoordinateProperties d c₀ (rightChartCandidate S C z m)
        (n04bRightRootFlow C L z m) ρ 1 G := by
  obtain ⟨ρ, d, c₀, G, hρ, hsmall, hG, _⟩ :=
    n04b_exists_right_physical_root_coordinate_with_halfGap hT hS h03 hL hz hs m
  exact ⟨ρ, d, c₀, G, hρ, hsmall, hG⟩

end ContinuousFlexibility.Analysis
