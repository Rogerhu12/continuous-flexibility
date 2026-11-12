import ContinuousFlexibility.Analysis.N07aCoefficientParameterJets
import ContinuousFlexibility.Analysis.N01JetBounds
import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# One actual coefficient tower with the original sampled height gain

The N01 estimates may choose a scalar directional tower separately for
each requested pair of orders. Uniqueness of genuine directional jets
identifies every such choice with the already chosen coefficient tower.
The affine sector restriction and the product of all scalar coordinates
therefore retain one tower, the exact sample, and the full H^(3/4) gain.
No moving canonical coordinate or its derivative is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

attribute [local instance]
  n07aNonlinearAnnularGroup
  n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup
  n07aNonlinearAnnularSMul
  n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup
  n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup
  n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup
  n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup
  n07aNonlinearDirectionsSMul
  n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup
  n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup
  n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The same chosen scalar tower obeys the original cell estimate at
every parameter and spatial order, without absorbing its height gain. -/
theorem n04CoefficientTower_materialSample_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (i : Fin 3) (a b : ℕ) (p : annularOpen D),
      a + b ≤ s → p.val.1 ∈ D.cells m →
      ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |(n07aCoefficientTower hT h01 i a b p).D k z v| ≤
          B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
            oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
              base (s + loss) (z - (C.referenceState, 0)) v := by
  obtain ⟨B, hB, hbound⟩ := (n01CoefficientJetBounds_of_properties h01) k s
  refine ⟨B, hB, ?_⟩
  intro m i a b p hab hp z hz v
  obtain ⟨J, hJ⟩ := hbound m i a b p.val hab hp
  rw [n07aCoefficientTower_unique hT h01 i a b p J k hz]
  exact hJ z hz v

/-- Affine restriction preserves the exact sampled coefficient and
height factors, as well as the original one-high-direction expression. -/
theorem n04CoefficientParameterJet_materialSample_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (i : Fin 3) (a b : ℕ) (p : annularOpen D),
      a + b ≤ s → p.val.1 ∈ D.cells m →
      ∀ z : StateDirections S × ℝ, z ∈ sectorNeighborhood S base ε ε →
      ∀ v : Fin k → (StateDirections S × ℝ),
        |(n07aCoefficientParameterJet hT h01 i a b p).D k z v| ≤
          B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
            oneHighVariationWeight (n07aParameterGrading S) base (s + loss) z v := by
  obtain ⟨B, hB, hbound⟩ := n04CoefficientTower_materialSample_bound hT h01 k s
  refine ⟨B, hB, ?_⟩
  intro m i a b p hab hp z hz v
  have h := hbound m i a b p hab hp (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (fun j => n07aSectorParameterInclusion S (v j))
  rw [n07aCoefficientParameterJet_D]
  have hw := n07aSectorParameterVariation_eq S C base (s + loss) z v
  change oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
      base (s + loss) (liftSectorParameter S C z - (C.referenceState, 0))
      (fun j => n07aSectorParameterInclusion S (v j)) =
    oneHighVariationWeight (n07aParameterGrading S) base (s + loss) z v at hw
  rw [hw] at h
  exact h

/-- Every actual physical coefficient-difference jet, in one product. -/
def n04CoefficientSampleJetField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ) :
    Fin 3 → ℕ → ℕ → annularOpen D → ℝ :=
  fun i a b p => mixedDerivative a b
    (n07aCoefficientDifferenceField D S C i (liftSectorParameter S C z)) p.val

/-- The product topology needs no finite index assumption. Each scalar
coordinate contributes its genuine continuity and derivative recurrence. -/
def n04CoefficientSampleJetTower
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (n04CoefficientSampleJetField D S C) :=
  smoothDirectionsScalarPi (n07a_sectorNeighborhood_isOpen S base ε ε) (fun i =>
    smoothDirectionsScalarPi (n07a_sectorNeighborhood_isOpen S base ε ε) (fun a =>
      smoothDirectionsScalarPi (n07a_sectorNeighborhood_isOpen S base ε ε) (fun b =>
        smoothDirectionsScalarPi (n07a_sectorNeighborhood_isOpen S base ε ε)
          (fun p => n07aCoefficientParameterJet hT h01 i a b p))))

theorem n04CoefficientSampleJetTower_D
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (k : ℕ) (z : StateDirections S × ℝ) (v : Fin k → (StateDirections S × ℝ))
    (i : Fin 3) (a b : ℕ) (p : annularOpen D) :
    (n04CoefficientSampleJetTower hT h01).D k z v i a b p =
      (n07aCoefficientParameterJet hT h01 i a b p).D k z v := by
  simp only [n04CoefficientSampleJetTower, smoothDirectionsScalarPi,
    ContinuousMultilinearMap.pi_apply]

/-- A single all-order physical coefficient tower has the original
sampled H^(3/4) estimate simultaneously for all scalar coordinates. -/
theorem n04CoefficientSampleJetTower_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (i : Fin 3) (a b : ℕ) (p : annularOpen D),
      a + b ≤ s → p.val.1 ∈ D.cells m →
      ∀ z : StateDirections S × ℝ, z ∈ sectorNeighborhood S base ε ε →
      ∀ v : Fin k → (StateDirections S × ℝ),
        |(n04CoefficientSampleJetTower hT h01).D k z v i a b p| ≤
          B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
            oneHighVariationWeight (n07aParameterGrading S) base (s + loss) z v := by
  obtain ⟨B, hB, hbound⟩ := n04CoefficientParameterJet_materialSample_bound hT h01 k s
  refine ⟨B, hB, ?_⟩
  intro m i a b p hab hp z hz v
  rw [n04CoefficientSampleJetTower_D]
  exact hbound m i a b p hab hp z hz v

end ContinuousFlexibility.Analysis
