import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsBoundaryFormulas
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPowerTrace
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsUnitTraces
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootOddLower

/-!
# The finite original odd trace packet

The packet consists of the four already identified odd boundary
formulas. Positivity follows from the actual factored speed and forward
label slope on the same root strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PositiveOddTraceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04PositiveGeometry_rootOddTrace
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (j : ℕ)
    (y : (StateDirections S × ℝ) × ℝ) : ℝ :=
  if hj : j ≤ 3 then
    n04PositiveGeometry_rootBoundaryFormula D S C g m side ⟨4 + j, by omega⟩ y
  else 0

theorem n04PositiveGeometry_rootOddTrace_eq
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (j : ℕ) (hj : j ≤ 3) :
    n04PositiveGeometry_rootOddTrace D S C g m side j =
      n04PositiveGeometry_rootBoundaryFormula D S C g m side ⟨4 + j, by omega⟩ := by
  funext y
  simp only [n04PositiveGeometry_rootOddTrace, dif_pos hj]

def n04PositiveGeometry_rootOddTrace_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0)
    (m : ℕ) (side : Bool) (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0) (j : ℕ) (hj : j ≤ 3) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootOddTrace D S C g m side j) := by
  rw [n04PositiveGeometry_rootOddTrace_eq D S C g m side j hj]
  exact n04PositiveGeometry_rootBoundaryFormula_joint hT hS hN hε
    g hg hg0 m side hr hroot ⟨4 + j, by omega⟩

theorem n04PositiveGeometry_rootOddTrace_zero_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) {ρ : ℝ} (hρ : 0 < ρ)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (hstrip : RootCoefficientStripConditions D.w g
      (stateProfile D S C (liftSectorParameter S C z).1)
      (stateHeight D S C (liftSectorParameter S C z))
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) ρ) (θ : ℝ) :
    0 < n04PositiveGeometry_rootOddTrace D S C g m side 0 (z, θ) := by
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-ρ - ρ) (ρ + ρ) ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith only [hρ], by linarith only [hρ]⟩, mem_univ _⟩
  have hs := hstrip (0, θ) hzero
  have hc := factoredCharacteristicSpeed_pos hs.1 hs.2.1 hs.2.2.1
    hs.2.2.2.1 hs.2.2.2.2.1
  have hβ := (n01RootLabel_deriv_mem_quarter_four hN hflow
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) m side θ).1
  change 0 < (2 / 3 : ℝ) * factoredCharacteristicSpeed D.w g
    (stateProfile D S C (liftSectorParameter S C z).1)
    (stateHeight D S C (liftSectorParameter S C z))
    (n01ComponentRoot C m side) (n01ComponentRootOrientation side) (0, θ) *
      deriv (n01RootLabel S C (liftSectorParameter S C z) m side) θ
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) hc)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hβ)

def n04PositiveGeometry_rootOddPowerTrace
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (γ : ℝ) (n : ℕ)
    (y : (StateDirections S × ℝ) × ℝ) : ℝ :=
  n04PositiveGeometry_rootPowerTrace γ n
    (fun j => n04PositiveGeometry_rootOddTrace D S C g m side j y)

end ContinuousFlexibility.Analysis
