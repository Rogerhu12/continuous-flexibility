import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseScale
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightTrace

/-!
# The joint inverse radial scale

This module isolates one stage of the actual inverse differential.
The original state, functions and derivative budgets are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04RootInverseScaleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n04PositiveGeometry_rootBoundaryInverseScale_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0)
    (m : ℕ) (side : Bool) (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    {R : ℝ} (hR : 0 < R)
    (hstrip : ∀ x ∈ sectorNeighborhood S base ε ε,
      RootCoefficientStripConditions D.w g
        (stateProfile D S C (liftSectorParameter S C x).1)
        (stateHeight D S C (liftSectorParameter S C x))
        (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y => (n04PositiveGeometry_rootBoundaryScale D S C g m side y)⁻¹) := by
  let J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootOddPowerTrace D S C g m side (-(2 / 3 : ℝ)) 0) :=
    n04PositiveGeometry_rootOddPowerTrace_joint hT hS hN hε hflow
      g hg hg0 m side hr hroot hR hstrip (-(2 / 3 : ℝ)) 0 (by omega)
  apply (smoothDirections_postcompCLM J
    ((3 / 2 : ℝ) ^ (-(2 / 3 : ℝ)) • ContinuousLinearMap.id ℝ ℝ)).congr
  intro y hy
  exact (n04PositiveGeometry_rootBoundaryScale_inv_eq D S C g m side y
    (n04PositiveGeometry_rootOddTrace_zero_pos hT hS hN hflow
      g m side hR hy.1 (hstrip y.1 hy.1) y.2).le).symm

end ContinuousFlexibility.Analysis
