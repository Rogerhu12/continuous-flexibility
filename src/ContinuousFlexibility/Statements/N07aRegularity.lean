module

public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Actual intermediate targets for N07a

The angular target concerns the same relative inverse supplied by N06.
The linear target is precisely the equation, uniqueness and fixed-loss
estimate of the final scalar inverse. Neither is added to N06: the three
N07a subnodes prove these conclusions in manuscript order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- Every weighted realization is a realization of the original base
relative inverse, with one state factor carrying the high order. -/
def N07aAngularProperties (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (V : VolumeModelData S K) (b : ℕ)
    (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)
    (base : ℕ) (ε : ℝ) : Prop :=
  ∃ d : ℕ, ∀ t s : ℕ, ∃ Cts : ℝ, 0 < Cts ∧
    ∀ z ∈ sectorNeighborhood S base ε ε,
    ∀ F₀ : V.level (3 / 4 : ℝ) 0 b,
    ∀ Fts : V.level (3 / 4 : ℝ) (t : ℝ) (b + s),
      V.forget (3 / 4 : ℝ) (t : ℝ) (b + s) Fts =
        V.forget (3 / 4 : ℝ) 0 b F₀ →
      ∃ Qts : V.level (3 / 4 : ℝ) (t : ℝ) (b + s),
        V.forget (3 / 4 : ℝ) (t : ℝ) (b + s) Qts =
          V.forget (3 / 4 : ℝ) 0 b (P.inverse (liftSectorParameter S C z) F₀) ∧
        ‖Qts‖ ≤ Cts * (‖Fts‖ +
          (1 + CanonicalGeometry.parameterGrading S (b + t + s + d) z) * ‖F₀‖)

/-- The first three clauses of the frozen scalar inverse target. -/
def ScalarLinearInverseProperties (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (G : ScalarInverseData S) (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
  (∀ z ∈ U, stateSector S z.1 → ∀ f : S.Source,
    referenceRow D (heightPairField S (G.G z f).1) = 0 ∧
    (∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients z) (heightPairField S (G.G z f).1) p +
        (G.G z f).2 * nuColumnField D S C z p =
          (S.height (3 / 4 : ℝ)).decode f.val p)) ∧
  (∀ z ∈ U, stateSector S z.1 → ∀ η : HeightPair S, ∀ μ : ℝ, ∀ f : S.Source,
    referenceRow D (heightPairField S η) = 0 →
    (∀ p ∈ annularOpen D, divergenceOperator (L.coefficients z) (heightPairField S η) p +
      μ * nuColumnField D S C z p = (S.height (3 / 4 : ℝ)).decode f.val p) →
      G.G z f = (η, μ)) ∧
  LinearFamilyTame (pairGrading (sectorGrading S) realGrading)
    (pairGrading (heightPairGrading S) realGrading) S.sourceGrading
    (sectorNeighborhood S base ε ε)
    (fun z => (G.G (liftSectorParameter S C z)).toLinearMap)

end ContinuousFlexibility.Statements
