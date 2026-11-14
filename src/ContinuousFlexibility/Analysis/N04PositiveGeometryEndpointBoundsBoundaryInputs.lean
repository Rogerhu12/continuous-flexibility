module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsSampleCoefficients
public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledForwardLabelPrefix
public import ContinuousFlexibility.Analysis.N06RootBoundaryFiniteFormulas

/-!
# Genuine inputs of the finite root boundary formulas

These are the literal drift and factored speed at the original root,
with the forward root-label slope. Each of the nine joint towers is
constructed from the actual state fields before estimating its jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PositiveBoundaryInputStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private def rootInputSelect {α : Fin 9 → Type*}
    (a0 : α 0) (a1 : α 1) (a2 : α 2) (a3 : α 3) (a4 : α 4)
    (a5 : α 5) (a6 : α 6) (a7 : α 7) (a8 : α 8) (j : Fin 9) : α j :=
  Fin.cases (motive := α) a0
    (Fin.cases a1
      (Fin.cases a2
        (Fin.cases a3
          (Fin.cases a4
            (Fin.cases a5
              (Fin.cases a6
                (Fin.cases a7
                  (Fin.cases a8 (fun l : Fin 0 => Fin.elim0 l))))))))) j

private def rootInputDirections
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] {U : Set Y}
    (d c : Y → PolarPoint → ℝ) (β : Y → ℝ → ℝ)
    (Jd : ∀ a : ℕ, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun y : Y × ℝ => radialBoundaryJet (d y.1) 0 a y.2))
    (Jc : ∀ a : ℕ, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun y : Y × ℝ => radialBoundaryJet (c y.1) 0 a y.2))
    (JB : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun y : Y × ℝ => deriv (β y.1) y.2)) (j : Fin 9) :
    SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun y : Y × ℝ => n06RootBoundaryInputs (d y.1) (c y.1) (β y.1) j y.2) :=
  rootInputSelect (α := fun l : Fin 9 =>
      SmoothDirections (U ×ˢ (univ : Set ℝ))
        (fun y : Y × ℝ => n06RootBoundaryInputs (d y.1) (c y.1) (β y.1) l y.2))
    (Jd 0) (Jd 1) (Jd 2) (Jd 3) (Jc 0) (Jc 1) (Jc 2) (Jc 3) JB j

theorem n04PositiveGeometry_rootBoundaryInputs_each
    {Y : Type*} (d c : Y → PolarPoint → ℝ) (β : Y → ℝ → ℝ)
    (P : (Y → ℝ → ℝ) → Prop)
    (hd : ∀ a : ℕ, a ≤ 3 →
      P (fun y => radialBoundaryJet (d y) 0 a))
    (hc : ∀ a : ℕ, a ≤ 3 →
      P (fun y => radialBoundaryJet (c y) 0 a))
    (hβ : P (fun y => deriv (β y))) (j : Fin 9) :
    P (fun y => n06RootBoundaryInputs (d y) (c y) (β y) j) := by
  fin_cases j
  · exact hd 0 (by decide)
  · exact hd 1 (by decide)
  · exact hd 2 (by decide)
  · exact hd 3 (by decide)
  · exact hc 0 (by decide)
  · exact hc 1 (by decide)
  · exact hc 2 (by decide)
  · exact hc 3 (by decide)
  · exact hβ

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
  let JC (speed : Bool) (a : ℕ) :
      SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
        (fun y : (StateDirections S × ℝ) × ℝ => radialBoundaryJet
          (n04PositiveGeometry_rootRawCoefficient D S C g
            (n01ComponentRoot C m side) (n01ComponentRootOrientation side) speed
            (liftSectorParameter S C y.1)) 0 a y.2) :=
    n04PositiveGeometry_rootRawCoefficientTrace_joint hT hS hN hε hr hroot
      (n01ComponentRootOrientation side) g hg hg0 speed a
  let JB : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × ℝ =>
        deriv (n01RootLabel S C (liftSectorParameter S C y.1) m side) y.2) :=
    (smoothDirections_angularIterate
    (n04Realization_rootLabel_forwardJointDirections hT hS hN m side) 1).congr
      (fun _ _ => by simp only [iteratedDeriv_one])
  exact rootInputDirections
    (fun y => n04PositiveGeometry_rootRawCoefficient D S C g
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) false
      (liftSectorParameter S C y))
    (fun y => n04PositiveGeometry_rootRawCoefficient D S C g
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) true
      (liftSectorParameter S C y))
    (fun y => n01RootLabel S C (liftSectorParameter S C y) m side)
    (JC false) (JC true) JB j

end ContinuousFlexibility.Analysis
