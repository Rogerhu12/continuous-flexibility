module

public import ContinuousFlexibility.Analysis.N04RealizationConstantShiftUniform
public import ContinuousFlexibility.Analysis.N01OriginalCoefficientTameBounds
public import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
public import ContinuousFlexibility.Analysis.N04SignedPieces

/-!
# The actual coefficient towers on the whole annulus

The N01 increment estimate is uniform in its cell label. Selecting a
cell containing each physical radius therefore gives the genuine mixed
parameter towers on the whole annulus. This selection is used only to
identify the unique derivatives of the same coefficient function; it
does not change any canonical cell or material sample.

The actual reference coefficient is restored at every mixed spatial
order. Its uniform reference bound gives the seminorm bounds needed for
the existing two-coordinate joint construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04RealizationCoefficientAnnularStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n04Realization_annularCoefficientIncrementTower
    (hN : N01Properties D T S C base loss ε)
    (i : Fin 3) (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => coefficientFamily D S C i a b p (liftSectorParameter S C z)) :=
  hN.sectorCoefficientTower (n04CellAt D p.1) i a b p
    (n04_cell_at_mem hN.1.1.choose_spec.2.1 hp.1)

theorem n04Realization_annularCoefficientIncrement_uniform
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (i : Fin 3) (a b : ℕ) :
    UniformScalarJetSeminormBounds
      (fun p : annularOpen D =>
        n04Realization_annularCoefficientIncrementTower hN i a b p p.property) := by
  apply uniformScalarJetSeminormBounds_of_oneHigh
    (pairGrading (sectorGrading S) realGrading)
    (sectorPairGrading_continuous S) (sectorPairGrading_monotone S)
    base (fun _ => a + b + loss)
  intro n
  let data := hN.sectorCoefficientTower_uniform_oneHigh hT n (a + b)
  refine ⟨data.choose, data.choose_spec.1, ?_⟩
  intro p z hz v
  exact data.choose_spec.2 (n04CellAt D p.val.1) i a b p.val le_rfl
    (n04_cell_at_mem hN.1.1.choose_spec.2.1 p.property.1) z hz v

theorem n04Realization_coefficientMixed_eq_increment_add
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (i : Fin 3) (a b : ℕ) {p : PolarPoint} (hp : p ∈ annularOpen D)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε) :
    mixedDerivative a b
        (originalCoefficientEntry D S C i (liftSectorParameter S C z)) p =
      coefficientFamily D S C i a b p (liftSectorParameter S C z) +
        mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p := by
  have hcurrent := hN.original_coefficient_contDiffOn hS hT
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) i
  have href := hN.original_coefficient_contDiffOn hS hT hN.reference_mem_stateNeighborhood
    hN.2.2.1.stateSector i
  have hdiff := mixedDerivative_sub_of_contDiffOn
    (isOpen_Ioo.prod isOpen_univ) hcurrent href a b hp
  have hdiff' : coefficientFamily D S C i a b p (liftSectorParameter S C z) =
      mixedDerivative a b
        (originalCoefficientEntry D S C i (liftSectorParameter S C z)) p -
      mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p := hdiff
  exact eq_add_of_sub_eq hdiff'.symm

def n04Realization_annularOriginalMixedTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (i : Fin 3) (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative a b
        (originalCoefficientEntry D S C i (liftSectorParameter S C z)) p) := by
  let c : ℝ :=
    mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p
  let K := (smoothDirectionsLinear (ContinuousLinearMap.id ℝ ℝ)).compAffine
    (0 : (StateDirections S × ℝ) →L[ℝ] ℝ) c
    (sectorNeighborhood_isOpen S base ε ε) (fun _ _ => mem_univ _)
  apply (smoothDirectionsAdd
    (n04Realization_annularCoefficientIncrementTower hN i a b p hp) K).congrOn
  intro z hz
  simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, add_zero] using
    (n04Realization_coefficientMixed_eq_increment_add hN hS hT i a b hp hz).symm

theorem n04Realization_annularOriginalMixed_uniform
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (i : Fin 3) (a b : ℕ) :
    UniformScalarJetSeminormBounds
      (fun p : annularOpen D =>
        n04Realization_annularOriginalMixedTower hN hS hT i a b p p.property) := by
  let data := hN.reference_coefficient_mixed_uniform_bound (a + b)
  exact n04Realization_uniformSeminormBounds_of_constantShift
    (fun p : annularOpen D =>
      n04Realization_annularOriginalMixedTower hN hS hT i a b p p.property)
    (fun p : annularOpen D =>
      n04Realization_annularCoefficientIncrementTower hN i a b p p.property)
    (fun p : annularOpen D =>
      mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p)
    (fun p _ hz =>
      n04Realization_coefficientMixed_eq_increment_add hN hS hT i a b p.property hz)
    (n04Realization_annularCoefficientIncrement_uniform hN hT i a b)
    data.choose_spec.1
    (fun p => data.choose_spec.2 i a b le_rfl p p.property)

def n04Realization_annularOriginalMixedRegularity
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (i : Fin 3) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) (annularOpen D)
      (fun z => originalCoefficientEntry D S C i (liftSectorParameter S C z)) where
  spatial z hz := hN.original_coefficient_contDiffOn hS hT
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) i
  parameter := n04Realization_annularOriginalMixedTower hN hS hT i

end ContinuousFlexibility.Analysis
