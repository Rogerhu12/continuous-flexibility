import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseScale
import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInversePacket
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightTrace
import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryDirections

/-!
# The actual inverse root differential as a joint tower

The inverse radial scale is a fixed multiple of the zeroth odd trace
to power `-2/3`. Both physical coefficients are evaluated at the genuine
inverse label. Its ordinary slope supplies the remaining coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04RootInverseDirectionsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private theorem inverseScaleCoefficient_le_one :
    |(3 / 2 : ℝ) ^ (-(2 / 3 : ℝ))| ≤ 1 := by
  rw [abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n04PositiveGeometry_rootInverseDerivative_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (side : Bool) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × ℝ =>
        deriv (Function.invFun (n01RootLabel S C (liftSectorParameter S C y.1) m side)) y.2) :=
  (smoothDirections_angularIterate
    (n04Realization_rootLabel_inverseJointDirections hT hS hN m side) 1).congr
      (fun _ _ => by simp only [iteratedDeriv_one])

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

/-- This tower is for the literal inverse differential already
identified with the original stored inverse chart. -/
def n04PositiveGeometry_rootInverseDifferential_joint
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
      (n04PositiveGeometry_rootInverseDifferential D S C g m side) := by
  letI : LocallyConvexSpace ℝ (StateDirections S × ℝ) :=
    (sectorPairGrading_withSeminorms S).toLocallyConvexSpace
  let JP : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootInverseDifferentialPacket D S C g m side) :=
    n04PositiveGeometry_rootInversePacket_joint (n01ComponentRootOrientation side)
      ((3 / 2 : ℝ) ^ (-(2 / 3 : ℝ)))
      (n04PositiveGeometry_rootOddPowerTrace_joint hT hS hN hε hflow
        g hg hg0 m side hr hroot hR hstrip (-(2 / 3 : ℝ)) 0 (by omega))
      (n04PositiveGeometry_rootBoundaryFormula_joint hT hS hN hε
        g hg hg0 m side hr hroot 0)
      (n04PositiveGeometry_rootInverseDerivative_joint hT hS hN m side)
      (n04Realization_rootLabel_inverseJointDirections hT hS hN m side)
  apply JP.congr
  intro y hy
  exact (n04PositiveGeometry_rootInverseDifferential_packet_eq D S C g m side y
    (n04PositiveGeometry_rootOddTrace_zero_pos hT hS hN hflow
      g m side hR hy.1 (hstrip y.1 hy.1)
      (Function.invFun (n01RootLabel S C (liftSectorParameter S C y.1) m side) y.2)).le).symm

/-- The quantitative bridge consumes the true odd negative power and
even trace at the inverse angle, together with positive inverse-label
words and its slope. Constants precede all state and scalar data. -/
theorem n04PositiveGeometry_rootInverseDifferential_word_bound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K s : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ degree : ℕ, 1 ≤ degree ∧
    ∀ (g : ℝ → ℝ) (m : ℕ) (side : Bool) {U : Set (StateDirections S × ℝ)}, IsOpen U →
    ∀ JO : SmoothDirections (U ×ˢ univ)
      (n04PositiveGeometry_rootOddPowerTrace D S C g m side (-(2 / 3 : ℝ)) 0),
    ∀ JE : SmoothDirections (U ×ˢ univ)
      (n04PositiveGeometry_rootBoundaryFormula D S C g m side 0),
    ∀ Jα : SmoothDirections (U ×ˢ univ) (fun y : (StateDirections S × ℝ) × ℝ =>
      Function.invFun (n01RootLabel S C (liftSectorParameter S C y.1) m side) y.2),
    ∀ Jb : SmoothDirections (U ×ˢ univ) (fun y : (StateDirections S × ℝ) × ℝ =>
      deriv (Function.invFun (n01RootLabel S C (liftSectorParameter S C y.1) m side)) y.2),
    ∀ Q : SmoothDirections (U ×ˢ univ) (n04PositiveGeometry_rootInverseDifferential D S C g m side),
    (∀ y ∈ U ×ˢ (univ : Set ℝ), 0 ≤ n04PositiveGeometry_rootOddTrace D S C g m side 0 y) →
    ∀ x ∈ U, ∀ θ, ∀ p q : Seminorm ℝ (StateDirections S × ℝ), ∀ R : ℝ, 0 ≤ R →
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → H ≤ L → 1 ≤ t → ∀ shift : ℕ,
    let P := fun v => p v ≤ 1 ∧ q v ≤ R
    let η := Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) θ
    N04BoundaryWordBounds JO K (s + K) 1 x η P M H t shift →
    N04BoundaryWordBounds JE K (s + K) 1 x η P M H t shift →
    N04BoundaryPositiveWordBounds Jα K (s + K) 1 x θ P M H t shift →
    N04BoundaryWordBounds Jb K s 1 x θ P M H t shift →
    N04BoundaryWordBounds Q K s 1 x θ P (A * M ^ degree) H t (shift + 1) := by
  letI : LocallyConvexSpace ℝ (StateDirections S × ℝ) :=
    (sectorPairGrading_withSeminorms S).toLocallyConvexSpace
  obtain ⟨A, hA, degree, hd, hbound⟩ :=
    n04PositiveGeometry_rootInversePacket_word_bound (E := StateDirections S × ℝ) K s L hL
  refine ⟨A, hA, degree, hd, ?_⟩
  intro g m side U hU JO JE Jα Jb Q hpos x hx θ p q R hR M H t hM hH hHM hHL ht shift
  dsimp only
  intro hO hE hα hb
  have heq (y : (StateDirections S × ℝ) × ℝ) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :=
    n04PositiveGeometry_rootInverseDifferential_packet_eq D S C g m side y
      (hpos (y.1, Function.invFun
        (n01RootLabel S C (liftSectorParameter S C y.1) m side) y.2) ⟨hy.1, mem_univ _⟩)
  let QP : SmoothDirections (U ×ˢ univ)
      (n04PositiveGeometry_rootInverseDifferentialPacket D S C g m side) := Q.congr heq
  have hpacket := hbound hU JO JE Jb Jα
    (n01ComponentRootOrientation side) (n01ComponentRootOrientation_eq side)
    ((3 / 2 : ℝ) ^ (-(2 / 3 : ℝ))) inverseScaleCoefficient_le_one QP
    x hx θ p q R hR M H t hM hH hHM hHL ht shift hO hE hα hb
  exact hpacket.congr (Q := Q) hx (fun y hy => (heq y hy).symm)

end ContinuousFlexibility.Analysis
