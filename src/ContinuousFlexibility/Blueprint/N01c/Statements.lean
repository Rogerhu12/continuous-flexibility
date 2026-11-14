module

public import ContinuousFlexibility.Blueprint.Statements

/-!
# The coefficient, speed and flow stages of N01c

These are concrete existential stages of the same construction.  A stage
may choose the geometry and then a smaller common neighbourhood; no stage
claims that an arbitrary unlocalized witness of N01b has quantitative flow
bounds.  All families below are the actual coefficients and speeds from
`Statements.Nonlinear`, not abstract substitutes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

/-- The coefficient stage retains all of N01b and supplies the actual
uniform coefficient estimates on its chosen common neighbourhood. -/
def N01CoefficientStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ base loss : ℕ, ∃ ε : ℝ,
      IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
        N01PartA A.val T S C ∧ 0 < ε ∧ N01PartB A.val S C base ε ∧
          CoefficientFamilyTameBounds A.val T S C base loss ε ∧
            N01PrimitiveGeometry A.val T S C ∧
              ∀ r ∈ Ioo A.val.a A.val.b, 1 ≤ T.E0 r

/-- The speed difference is evaluated in the physical radial and angular
coordinates, exactly as in the ordinary ODE in `ordinaryFlowConditions`. -/
def characteristicSpeedFamily (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (a b : ℕ) (p : PolarPoint)
    (z : AnnularState S × ℝ) : ℝ :=
  mixedDerivative a b (fun x =>
    minusCharacteristicSpeed (originalCoefficients D S C z) x -
      minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0)) x) p

/-- Quantitative speed input for the ODE estimate.  Spatial smoothness is
asserted separately: a totalized `iteratedDeriv` alone does not establish it.
Endpoint distances compensate for radial differentiation at the simple roots.
One base and radius work at every order; only the parameter loss and constants
may depend on the parameter differentiation order. -/
def CharacteristicSpeedTameBounds (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  (∀ z ∈ stateNeighborhood S C base ε, ∀ m,
    ContDiffOn ℝ ∞ (minusCharacteristicSpeed (originalCoefficients D S C z))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))) ∧
  (∀ k : ℕ, ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m a b p,
    a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
    ∃ J : SmoothDirections (stateNeighborhood S C base ε)
        (characteristicSpeedFamily D S C a b p),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss + parameterLoss) (z - (C.referenceState, 0)) v)

/-- The speed stage carries the coefficient conclusion forward with the
quantitative, smooth speed family needed for the ordinary-flow variations. -/
def N01SpeedStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ base loss : ℕ, ∃ ε : ℝ,
      IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
        N01PartA A.val T S C ∧ 0 < ε ∧ N01PartB A.val S C base ε ∧
          CoefficientFamilyTameBounds A.val T S C base loss ε ∧
            CharacteristicSpeedTameBounds A.val T S C base loss ε ∧
              N01PrimitiveGeometry A.val T S C ∧
                ∀ r ∈ Ioo A.val.a A.val.b, 1 ≤ T.E0 r

end ContinuousFlexibility.Blueprint
