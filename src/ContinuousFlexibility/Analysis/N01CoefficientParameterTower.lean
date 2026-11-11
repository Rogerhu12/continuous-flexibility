import ContinuousFlexibility.Analysis.SectorParameterGeometry
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Actual coefficient towers in sector parameters

The original N01 tower is restricted by the actual affine sector
inclusion. The same one-high bound survives with its original spatial
order budget. A canonical choice of genuine tower can therefore be used
at every parameter order, by uniqueness, without changing the estimate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01CoefficientParameterTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.sectorCoefficient_tower
    (hN : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m i a b p, a + b ≤ s → p.1 ∈ D.cells m →
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => coefficientFamily D S C i a b p (liftSectorParameter S C z)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample m) ^ B *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) z v := by
  let data := hN.2.2.2.2.2.2.2.2.2.2.2.1 k s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  refine ⟨B, hB, ?_⟩
  intro m i a b p hab hp
  let pointData := data.choose_spec.2 m i a b p hab hp
  let J := pointData.choose
  have hmap : MapsTo (fun z : StateDirections S × ℝ =>
      (C.referenceState, 0) + sectorParameterInclusion S z)
      (sectorNeighborhood S base ε ε) (stateNeighborhood S C base ε) := by
    intro z hz
    exact Eq.mp
      (congrArg (fun u : AnnularState S × ℝ => u ∈ stateNeighborhood S C base ε)
        (liftSectorParameter_eq_affine S C z))
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
  let K : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => coefficientFamily D S C i a b p (liftSectorParameter S C z)) :=
    (J.compAffine (sectorParameterInclusion S) (C.referenceState, 0)
      (sectorNeighborhood_isOpen S base ε ε) hmap).congrOn
      (fun z _ => congrArg (coefficientFamily D S C i a b p)
        (liftSectorParameter_eq_affine S C z).symm)
  refine ⟨K, ?_⟩
  intro z hz v
  have heq : K.D k z v = J.D k (liftSectorParameter S C z)
      (fun j => sectorParameterInclusion S (v j)) :=
    congrArg (fun y => J.D k y (fun j => sectorParameterInclusion S (v j)))
      (liftSectorParameter_eq_affine S C z).symm
  have hraw := pointData.choose_spec (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (fun j => sectorParameterInclusion S (v j))
  have hw := oneHighVariationWeight_sector_lift S C base (s + loss) z v
  exact (congrArg abs heq).trans_le (hraw.trans_eq
    (congrArg (fun W : ℝ => B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample m) ^ B * W) hw))

def N01Properties.sectorCoefficientTower
    (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (i : Fin 3) (a b : ℕ) (p : PolarPoint) (hp : p.1 ∈ D.cells m) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => coefficientFamily D S C i a b p (liftSectorParameter S C z)) :=
  ((hN.sectorCoefficient_tower 0 (a + b)).choose_spec.2 m i a b p le_rfl hp).choose

theorem N01Properties.sectorCoefficientTower_bound
    (hN : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m i a b p (hab : a + b ≤ s) (hp : p.1 ∈ D.cells m),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
        |(hN.sectorCoefficientTower m i a b p hp).D k z v| ≤
          B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) z v := by
  let data := hN.sectorCoefficient_tower k s
  refine ⟨data.choose, data.choose_spec.1, ?_⟩
  intro m i a b p hab hp z hz v
  let pointData := data.choose_spec.2 m i a b p hab hp
  let K := pointData.choose
  have heq := (hN.sectorCoefficientTower m i a b p hp).unique K k z hz
  exact (congrArg (fun A : (StateDirections S × ℝ) [×k]→L[ℝ] ℝ => |A v|) heq).trans_le
    (pointData.choose_spec z hz v)

/-- Restore the reference value after taking the actual N01 coefficient
increment. No parameter derivative of the reference is introduced. -/
def N01Properties.originalCoefficientSectorTower
    (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (i : Fin 3) (p : PolarPoint) (hp : p.1 ∈ D.cells m) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => if i = 0 then (originalCoefficients D S C (liftSectorParameter S C z)).a p
        else if i = 1 then (originalCoefficients D S C (liftSectorParameter S C z)).b p
        else (originalCoefficients D S C (liftSectorParameter S C z)).c p) := by
  let c : ℝ := if i = 0 then (originalCoefficients D S C (C.referenceState, 0)).a p
    else if i = 1 then (originalCoefficients D S C (C.referenceState, 0)).b p
    else (originalCoefficients D S C (C.referenceState, 0)).c p
  let K := (smoothDirectionsLinear (ContinuousLinearMap.id ℝ ℝ)).compAffine
    (0 : (StateDirections S × ℝ) →L[ℝ] ℝ) c
    (sectorNeighborhood_isOpen S base ε ε) (fun _ _ => mem_univ _)
  apply (smoothDirectionsAdd (hN.sectorCoefficientTower m i 0 0 p hp) K).congrOn
  intro z hz
  change coefficientFamily D S C i 0 0 p (liftSectorParameter S C z) + (c + 0) = _
  simp only [coefficientFamily, mixedDerivative, iteratedDeriv_zero, add_zero, c]
  split_ifs <;> ring

end ContinuousFlexibility.Statements
