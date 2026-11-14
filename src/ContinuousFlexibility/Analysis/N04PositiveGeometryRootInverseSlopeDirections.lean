import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryDirections
import ContinuousFlexibility.Analysis.N01cAngularJetTowers

/-!
# The joint inverse-label slope

This module isolates one stage of the actual inverse differential.
The original state, functions and derivative budgets are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04RootInverseSlopeStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n04PositiveGeometry_rootInverseDerivative_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (side : Bool) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × ℝ =>
        deriv (Function.invFun (n01RootLabel S C (liftSectorParameter S C y.1) m side)) y.2) := by
  let Jα : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × ℝ =>
        Function.invFun (n01RootLabel S C (liftSectorParameter S C y.1) m side) y.2) :=
    n04Realization_rootLabel_inverseJointDirections hT hS hN m side
  let J₁ : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × ℝ => iteratedDeriv 1
        (Function.invFun (n01RootLabel S C (liftSectorParameter S C y.1) m side)) y.2) :=
    smoothDirections_angularIterate Jα 1
  exact J₁.congr (fun _ _ => by simp only [iteratedDeriv_one])

end ContinuousFlexibility.Analysis
