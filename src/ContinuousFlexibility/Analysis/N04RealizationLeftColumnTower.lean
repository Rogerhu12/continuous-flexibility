import ContinuousFlexibility.Analysis.N04RealizationLeftReducedTower
import ContinuousFlexibility.Analysis.N04RealizationUniformAffineFamily
import ContinuousFlexibility.Analysis.N04RealizationUniformSector
import ContinuousFlexibility.Analysis.N07aNuSource

/-!
# The actual current left column with a uniform sector tower

The same affine state projection supplies the reduced left-height
column. One sector neighborhood supports the entire tower. Its decoder
equals the current physical divergence on the annulus and vanishes with
that divergence outside the annulus.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

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

private theorem n04Realization_leftColumn_affineDecoder
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (U : Set (N07aNuParameter S)) (N : N07aNuParameter S → ScalarHeightSpace S)
    (hgeometry : ∀ y ∈ U,
      ScalarStateGeometry D S (n07aNuParameterState hT hS h01.1.2.2.2.1 y))
    (hdecode : ∀ y ∈ U, ∀ p ∈ annularOpen D,
      (S.height scalarBeta).decode (N y) p =
        scalarStateOperator D S (n07aNuParameterState hT hS h01.1.2.2.2.1 y) (0, 1) p)
    {b : ℕ} {η : ℝ} (hb : base ≤ b) (hηε : η ≤ ε)
    (hmaps : sectorNeighborhood S b η η ⊆
      (fun z => n07aNuParameterCenter S C.referenceState.1.1 +
        n07aNuSectorProjectionCLM S z) ⁻¹' U) :
    ∀ z ∈ sectorNeighborhood S b η η, ∀ p,
      (S.height scalarBeta).decode
        (N (n07aNuParameterCenter S C.referenceState.1.1 +
          n07aNuSectorProjectionCLM S z)) p =
        n06CurrentLeftColumn S L (liftSectorParameter S C z) p := by
  intro z hz p
  by_cases hp : p ∈ annularOpen D
  · have hcoord : n07aNuParameterCenter S C.referenceState.1.1 +
        n07aNuSectorProjectionCLM S z =
        n07aNuRawProjectionCLM S (liftSectorParameter S C z) :=
      n07aNuSectorProjectionCLM_center h01.2.2.1 z
    have hy : n07aNuParameterState hT hS h01.1.2.2.2.1
        (n07aNuParameterCenter S C.referenceState.1.1 + n07aNuSectorProjectionCLM S z) =
        n07aNuScalarState hT hS h01.1.2.2.2.1 (liftSectorParameter S C z) := by
      rw [hcoord, n07aNuRawProjectionCLM_apply]
      rfl
    have hg : ScalarStateGeometry D S
        (n07aNuScalarState hT hS h01.1.2.2.2.1 (liftSectorParameter S C z)) :=
      hy ▸ hgeometry _ (hmaps hz)
    have hzold := sectorNeighborhood_mono S hb hηε hηε hz
    have hraw := liftSectorParameter_mem_stateNeighborhood (C := C) hzold le_rfl
    have hsector := h01.2.2.1.liftSectorParameter_sector z
    calc
      _ = scalarStateOperator D S
          (n07aNuParameterState hT hS h01.1.2.2.2.1
            (n07aNuParameterCenter S C.referenceState.1.1 +
              n07aNuSectorProjectionCLM S z)) (0, 1) p :=
        hdecode _ (hmaps hz) p hp
      _ = scalarStateOperator D S
          (n07aNuScalarState hT hS h01.1.2.2.2.1 (liftSectorParameter S C z))
          (0, 1) p := congrArg (fun x => scalarStateOperator D S x (0, 1) p) hy
      _ = _ := (n04Realization_actualLeft_eq_reduced hT hS h01 h03
        hraw hsector hg hp).symm
  · rw [scalarHeight_decode_eq_zero_outside hS _ hp]
    obtain ⟨J, _, hJD, _, hzero⟩ := n06_currentLeftColumns_commonSupport (L := L) hS
    exact (hzero (liftSectorParameter S C z) p.1
      (fun hpJ => hp ⟨hJD hpJ, mem_univ _⟩) p.2).symm

/-- The same corrected coefficient record has this actual height-valued
column on one fixed neighborhood, before all derivative orders. -/
theorem n04Realization_exists_uniformLeftColumn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) :
    ∃ b ell : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      ∃ N : (StateDirections S × ℝ) → ScalarHeightSpace S,
        FixedNeighborhoodSmoothTame (n07aParameterGrading S) (scalarHeightGrading S)
          (sectorNeighborhood S b η η) b ell N ∧
        (∀ z ∈ sectorNeighborhood S b η η, ∀ p,
          (S.height scalarBeta).decode (N z) p =
            n06CurrentLeftColumn S L (liftSectorParameter S C z) p) := by
  letI : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  exact n04Realization_uniformAffine_family
    (X := StateDirections S × ℝ) (Y := N07aNuParameter S) (Z := ScalarHeightSpace S)
    (n07aParameterGrading S) (n07aNuParameterGrading S) (scalarHeightGrading S)
    (n07aNuParameterCenter S C.referenceState.1.1) (n07aNuSectorProjectionCLM S)
    (n07aNuSectorProjectionCLM_grading_le S)
    (fun b η => sectorNeighborhood S b η η) base ε
    (fun U N =>
      (∀ y ∈ U, ScalarStateGeometry D S (n07aNuParameterState hT hS h01.1.2.2.2.1 y)) ∧
      (∀ y ∈ U, ∀ p ∈ annularOpen D, (S.height scalarBeta).decode (N y) p =
        scalarStateOperator D S (n07aNuParameterState hT hS h01.1.2.2.2.1 y) (0, 1) p))
    (fun b η N => ∀ z ∈ sectorNeighborhood S b η η, ∀ p,
      (S.height scalarBeta).decode (N z) p =
        n06CurrentLeftColumn S L (liftSectorParameter S C z) p)
    (fun W f b ell hW hzero hf =>
      n04Realization_fixedNeighborhood_sectorRestriction S (base := base)
        (towerBase := b) (loss := ell) (f := f) hW hzero hf h01.2.1)
    (fun U N hdecoded b η hb _ hηε hmaps =>
      n04Realization_leftColumn_affineDecoder hS hT h01 h03 U N
        hdecoded.1 hdecoded.2 hb hηε hmaps)
    (n04Realization_exists_uniformLeftReducedColumn h01.1.1 hT hS
      h01.1.2.2.2.1 C.referenceState.1.1)

end ContinuousFlexibility.Analysis
