import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsSampleCoefficients
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledForwardLabelPrefix
import ContinuousFlexibility.Analysis.N06RootBoundaryFiniteFormulas

/-!
# Genuine inputs of the finite root boundary formulas

These are the literal drift and factored speed at the original root,
with the forward root-label slope. Each of the nine joint towers is
constructed from the actual state fields before estimating its jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PositiveBoundaryInputStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04PositiveGeometry_rootBoundaryInput
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (j : Fin 9)
    (y : (StateDirections S × ℝ) × ℝ) : ℝ :=
  n06RootBoundaryInputs
    (n04PositiveGeometry_rootRawCoefficient D S C g
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) false
      (liftSectorParameter S C y.1))
    (n04PositiveGeometry_rootRawCoefficient D S C g
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) true
      (liftSectorParameter S C y.1))
    (n01RootLabel S C (liftSectorParameter S C y.1) m side) j y.2

theorem n04PositiveGeometry_rootBoundaryInput_eq
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (y : StateDirections S × ℝ) :
    (fun j θ => n04PositiveGeometry_rootBoundaryInput D S C g m side j (y, θ)) =
      n06RootBoundaryInputs
        (orientedCharacteristicDrift (stateProfile D S C (liftSectorParameter S C y).1)
          (stateHeight D S C (liftSectorParameter S C y))
          (n01ComponentRoot C m side) (n01ComponentRootOrientation side))
        (factoredCharacteristicSpeed D.w g
          (stateProfile D S C (liftSectorParameter S C y).1)
          (stateHeight D S C (liftSectorParameter S C y))
          (n01ComponentRoot C m side) (n01ComponentRootOrientation side))
        (n01RootLabel S C (liftSectorParameter S C y) m side) := rfl

def n04PositiveGeometry_rootBoundaryInput_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0)
    (m : ℕ) (side : Bool) (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0) (j : Fin 9) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootBoundaryInput D S C g m side j) := by
  let JC (speed : Bool) (a : ℕ) :=
    n04PositiveGeometry_rootRawCoefficientTrace_joint hT hS hN hε hr hroot
      (n01ComponentRootOrientation side) g hg hg0 speed a
  let JB : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × ℝ =>
        deriv (n01RootLabel S C (liftSectorParameter S C y.1) m side) y.2) :=
    (smoothDirections_angularIterate
    (n04Realization_rootLabel_forwardJointDirections hT hS hN m side) 1).congr
      (fun _ _ => by simp only [iteratedDeriv_one])
  exact Fin.cases (motive := fun l : Fin 9 =>
      SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
        (n04PositiveGeometry_rootBoundaryInput D S C g m side l))
    (JC false 0)
    (Fin.cases (JC false 1)
      (Fin.cases (JC false 2)
        (Fin.cases (JC false 3)
          (Fin.cases (JC true 0)
            (Fin.cases (JC true 1)
              (Fin.cases (JC true 2)
                (Fin.cases (JC true 3)
                  (Fin.cases JB (fun l : Fin 0 => Fin.elim0 l))))))))) j

end ContinuousFlexibility.Analysis
