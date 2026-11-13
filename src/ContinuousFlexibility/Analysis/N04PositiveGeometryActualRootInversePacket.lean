import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseScale
import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInversePacket

/-!
# The actual scalar packet identity

This module isolates one stage of the actual inverse differential.
The original state, functions and derivative budgets are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04ActualRootInversePacketStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04PositiveGeometry_rootInverseDifferentialPacket
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) :
    ((StateDirections S × ℝ) × ℝ) → PolarPoint →L[ℝ] PolarPoint :=
  n04PositiveGeometry_rootInversePacket (n01ComponentRootOrientation side)
    ((3 / 2 : ℝ) ^ (-(2 / 3 : ℝ)))
    (n04PositiveGeometry_rootOddPowerTrace D S C g m side (-(2 / 3 : ℝ)) 0)
    (n04PositiveGeometry_rootBoundaryFormula D S C g m side 0)
    (fun y => deriv (Function.invFun
      (n01RootLabel S C (liftSectorParameter S C y.1) m side)) y.2)
    (fun y => Function.invFun (n01RootLabel S C (liftSectorParameter S C y.1) m side) y.2)

theorem n04PositiveGeometry_rootInverseDifferential_packet_eq
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (y : (StateDirections S × ℝ) × ℝ)
    (hy : 0 ≤ n04PositiveGeometry_rootOddTrace D S C g m side 0
      (y.1, Function.invFun (n01RootLabel S C (liftSectorParameter S C y.1) m side) y.2)) :
    n04PositiveGeometry_rootInverseDifferential D S C g m side y =
      n04PositiveGeometry_rootInverseDifferentialPacket D S C g m side y := by
  dsimp only [n04PositiveGeometry_rootInverseDifferential,
    n04PositiveGeometry_rootInverseDifferentialPacket, n04PositiveGeometry_rootInversePacket]
  rw [n04PositiveGeometry_rootBoundaryScale_inv_eq D S C g m side _ hy]

end ContinuousFlexibility.Analysis
