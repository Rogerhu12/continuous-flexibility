import ContinuousFlexibility.Analysis.N01cActualFlowForcingComposition
import ContinuousFlexibility.Analysis.N01cFlowSlotBounds

/-!
# Indices for uniform estimates on the actual finite flow plots

This record only groups the original component, state, finite affine
map, and unit directions. Every function below is the previously
constructed actual coefficient, forcing factor, or ordinary variation.
Grouping the indices keeps existential constants outside the concrete
state-space representation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The original data of a finite affine plot, with its low unit-ball
condition. No flow estimate is part of this index. -/
structure OrdinaryFlowVariationInput
    (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) (N : ℕ) where
  component : ℕ
  tower : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
    (componentCosineSpeed D S C component)
  dimension : ℕ
  state : AnnularState S × ℝ
  mem : state ∈ stateNeighborhood S C base ε
  plot : (Fin dimension → ℝ) →L[ℝ] (AnnularState S × ℝ)
  directions : Fin N → (Fin dimension → ℝ)
  unit : ∀ i, pairGrading (stateGrading S) realGrading base (plot (directions i)) ≤ 1

namespace OrdinaryFlowVariationInput

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base N : ℕ} {ε : ℝ}

/-- One aggregate of the original state displacement and original
directions, before any interpolation. -/
def aggregate (u : OrdinaryFlowVariationInput D S C base ε N) (n : ℕ) : ℝ :=
  (1 + pairGrading (stateGrading S) realGrading n
    (u.state - (C.referenceState, 0))) +
      ∑ i, pairGrading (stateGrading S) realGrading n (u.plot (u.directions i))

theorem aggregate_one_le (u : OrdinaryFlowVariationInput D S C base ε N) (n : ℕ) :
    1 ≤ u.aggregate n := by
  have hx := apply_nonneg (pairGrading (stateGrading S) realGrading n)
    (u.state - (C.referenceState, 0))
  have hv : 0 ≤ ∑ i, pairGrading (stateGrading S) realGrading n
      (u.plot (u.directions i)) :=
    Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
  dsimp only [aggregate]
  linarith

theorem stateSize_le_aggregate
    (u : OrdinaryFlowVariationInput D S C base ε N) (n : ℕ) :
    1 + pairGrading (stateGrading S) realGrading n
      (u.state - (C.referenceState, 0)) ≤ u.aggregate n :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))

theorem aggregate_mono (u : OrdinaryFlowVariationInput D S C base ε N) :
    Monotone u.aggregate := by
  intro a b hab
  have hp := jointStateGrading_monotone S
  exact add_le_add
    (add_le_add_left (hp hab (u.state - (C.referenceState, 0))) 1)
    (Finset.sum_le_sum (fun i _ => hp hab (u.plot (u.directions i))))

/-- The same plot with one zero parameter direction. Its all-angle
singleton head is the actual linear coefficient at every variation order. -/
def angleInput (u : OrdinaryFlowVariationInput D S C base ε N) :
    OrdinaryFlowVariationInput D S C base ε 1 where
  component := u.component
  tower := u.tower
  dimension := u.dimension
  state := u.state
  mem := u.mem
  plot := u.plot
  directions := fun _ => 0
  unit := fun _ => by simp only [map_zero]; norm_num

theorem angleInput_aggregate_le
    (u : OrdinaryFlowVariationInput D S C base ε N) (n : ℕ) :
    u.angleInput.aggregate n ≤ u.aggregate n := by
  change (1 + pairGrading (stateGrading S) realGrading n
    (u.state - (C.referenceState, 0))) +
      (∑ _i : Fin 1, pairGrading (stateGrading S) realGrading n (u.plot 0)) ≤ _
  simp only [map_zero, Finset.sum_const_zero, add_zero]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))

variable {T : MaterialData}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
  (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
    r ∈ Icc (C.left i) (C.right i) →
      0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

def outerNorm (u : OrdinaryFlowVariationInput D S C base ε N)
    (s : ℕ) (t : ℝ) (ω : FlowForcingChoice N) : ℝ :=
  circleRealSobolevNorm (s : ℝ)
    (ordinaryFlowSpeedOuterJet hS hT hA hB hpos u.component u.state u.mem
      u.plot u.directions t ω 0)

def factorNorm (u : OrdinaryFlowVariationInput D S C base ε N)
    (s : ℕ) (t : ℝ) (ω : FlowForcingChoice N) (i : Fin (ω.1.length + 1)) : ℝ :=
  circleRealSobolevNorm (s : ℝ)
    (ordinaryFlowForcingFactorJet hS hT hA hB hpos u.component u.tower
      u.state u.mem u.plot u.directions t ω i 0)

def defectNorm (u : OrdinaryFlowVariationInput D S C base ε N)
    (s : ℕ) (t : ℝ) : ℝ :=
  circleRealSobolevNorm (s : ℝ)
    (ordinaryFlowFiniteDefectJet hS hT hA hB hpos u.component u.tower
      u.state u.mem u.plot t 0)

def data {n : ℕ} (u : OrdinaryFlowVariationInput D S C base ε (n + 1)) :
    CircleLinearVariationData Real.pi 0 1 :=
  ordinaryFlowCircleVariationData hS hT hA hB hpos u.component u.tower
    u.state u.mem u.plot n u.directions

theorem coefficientNorm_eq_angleHead {n : ℕ}
    (u : OrdinaryFlowVariationInput D S C base ε (n + 1)) (s : ℕ) (t : ℝ) :
    (u.data hS hT hA hB hpos).coefficientNorm s t =
      u.angleInput.factorNorm hS hT hA hB hpos s t flowAngleForcingChoice 0 := by
  change circleRealSobolevNorm (s : ℝ)
    ((ordinaryFlowCircleVariationData hS hT hA hB hpos u.component u.tower
      u.state u.mem u.plot n u.directions).coefficient t 0) = _
  rw [ordinaryFlowCircleVariationData_coefficient_eq_head]
  rfl

end OrdinaryFlowVariationInput

end ContinuousFlexibility.Statements
