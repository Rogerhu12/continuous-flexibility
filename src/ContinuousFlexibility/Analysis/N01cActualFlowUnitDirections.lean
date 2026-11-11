import ContinuousFlexibility.Analysis.N01cFlowVariationInput

/-!
# Recovering the original directions and physical radius

The finite affine chart built from a tuple sends its coordinate basis
to exactly that tuple. The two closed time surjections then evaluate
the same supplied ordinary trajectory at every physical radius.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base N : ℕ} {ε : ℝ}

/-- The canonical finite chart of an original tuple of state directions. -/
def ordinaryFlowVariationInputOfDirections
    (m : ℕ)
    (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m))
    (x : AnnularState S × ℝ) (hx : x ∈ stateNeighborhood S C base ε)
    (v : Fin N → (AnnularState S × ℝ))
    (hv : ∀ i, pairGrading (stateGrading S) realGrading base (v i) ≤ 1) :
    OrdinaryFlowVariationInput D S C base ε N where
  component := m
  tower := J
  dimension := N
  state := x
  mem := hx
  plot := finiteDirectionMap v
  directions := fun i => Pi.single i 1
  unit := fun i => by simpa only [finiteDirectionMap_single, one_smul] using hv i

theorem ordinaryFlowVariationInputOfDirections_aggregate
    (m : ℕ)
    (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m))
    (x : AnnularState S × ℝ) (hx : x ∈ stateNeighborhood S C base ε)
    (v : Fin N → (AnnularState S × ℝ))
    (hv : ∀ i, pairGrading (stateGrading S) realGrading base (v i) ≤ 1)
    (s : ℕ) :
    (ordinaryFlowVariationInputOfDirections m J x hx v hv).aggregate s =
      (1 + pairGrading (stateGrading S) realGrading s (x - (C.referenceState, 0))) +
        ∑ i, pairGrading (stateGrading S) realGrading s (v i) := by
  simp only [OrdinaryFlowVariationInput.aggregate, ordinaryFlowVariationInputOfDirections,
    finiteDirectionMap_single, one_smul]

variable {T : MaterialData}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
  (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
    r ∈ Icc (C.left i) (C.right i) →
      0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)

/-- Both surjections concern the original closed component. -/
include hA in
theorem exists_ordinaryFlowCompactTime_of_radius (m : ℕ) {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      rootCosinePath (C.left m) (C.right m) (circleFlowCompactTime 0 Real.pi t) = r := by
  obtain ⟨u, hu, hur⟩ := rootCosinePath_surjOn (hA.2.2.1.1 m).2.1 hr
  obtain ⟨t, ht, htu⟩ := circleFlowCompactTime_surjOn 0 Real.pi hu
  exact ⟨t, ht, by rw [htu, hur]⟩

theorem ordinaryFlowVariationInputOfDirections_value {n : ℕ}
    (m : ℕ)
    (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m))
    (x : AnnularState S × ℝ) (hx : x ∈ stateNeighborhood S C base ε)
    (v : Fin (n + 1) → (AnnularState S × ℝ))
    (hv : ∀ i, pairGrading (stateGrading S) realGrading base (v i) ≤ 1)
    (b : ℕ) (θ t r : ℝ)
    (hr : r ∈ Icc (C.left m) (C.right m))
    (ht : rootCosinePath (C.left m) (C.right m)
      (circleFlowCompactTime 0 Real.pi t) = r) :
    ((ordinaryFlowVariationInputOfDirections m J x hx v hv).data hS hT hA hB hpos).value t b (θ : AddCircle Real.pi) =
      (ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J hr b θ).D (n + 1) x v := by
  have he := ordinaryFlowCircleVariationData_value hS hT hA hB hpos m J x hx
    (finiteDirectionMap v) n (fun i => Pi.single i 1) t b θ
  rw [ht] at he
  simpa only [OrdinaryFlowVariationInput.data, ordinaryFlowVariationInputOfDirections,
    finiteDirectionMap_single, one_smul] using he

end ContinuousFlexibility.Statements
