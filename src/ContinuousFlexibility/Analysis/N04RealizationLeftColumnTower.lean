import ContinuousFlexibility.Analysis.N04RealizationLeftReducedTower
import ContinuousFlexibility.Analysis.N04RealizationUniformAffine
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
  obtain ⟨U, hU, hcenter, b₀, ell, N, hN, hgeometry, hdecode⟩ :=
    n04Realization_exists_uniformLeftReducedColumn h01.1.1 hT hS h01.1.2.2.2.1
      C.referenceState.1.1
  let c : N07aNuParameter S := n07aNuParameterCenter S C.referenceState.1.1
  let A : (StateDirections S × ℝ) → N07aNuParameter S :=
    fun z => c + n07aNuSectorProjectionCLM S z
  have hA : Continuous A := continuous_const.add (n07aNuSectorProjectionCLM S).continuous
  have hA0 : A (0 : StateDirections S × ℝ) = c := by
    simp only [A, map_zero, add_zero]
  have hzero : (0 : StateDirections S × ℝ) ∈ A ⁻¹' U :=
    hA0.symm ▸ hcenter
  have hpull : FixedNeighborhoodSmoothTame (n07aParameterGrading S)
      (scalarHeightGrading S) (A ⁻¹' U) b₀ ell (fun z => N (A z)) :=
    n04Realization_fixedNeighborhood_affine hN c (n07aNuSectorProjectionCLM S)
      (n07aNuSectorProjectionCLM_grading_le S)
  obtain ⟨b, η, hb, hη, hηε, hmaps, htower⟩ :=
    n04Realization_fixedNeighborhood_sectorRestriction S (base := base)
      (hU.preimage hA) hzero hpull h01.2.1
  refine ⟨b, ell, η, hb, hη, hηε, fun z => N (A z), htower, ?_⟩
  intro z hz p
  by_cases hp : p ∈ annularOpen D
  · have hcoord : A z = n07aNuRawProjectionCLM S (liftSectorParameter S C z) :=
      n07aNuSectorProjectionCLM_center h01.2.2.1 z
    have hy : n07aNuParameterState hT hS h01.1.2.2.2.1 (A z) =
        n07aNuScalarState hT hS h01.1.2.2.2.1 (liftSectorParameter S C z) := by
      rw [hcoord, n07aNuRawProjectionCLM_apply]
      rfl
    have hg : ScalarStateGeometry D S
        (n07aNuScalarState hT hS h01.1.2.2.2.1 (liftSectorParameter S C z)) :=
      hy ▸ hgeometry (A z) (hmaps hz)
    have hzold := sectorNeighborhood_mono S hb hηε hηε hz
    have hraw := liftSectorParameter_mem_stateNeighborhood (C := C) hzold le_rfl
    have hsector := h01.2.2.1.liftSectorParameter_sector z
    calc
      _ = scalarStateOperator D S
          (n07aNuParameterState hT hS h01.1.2.2.2.1 (A z)) (0, 1) p :=
        hdecode (A z) (hmaps hz) p hp
      _ = scalarStateOperator D S
          (n07aNuScalarState hT hS h01.1.2.2.2.1 (liftSectorParameter S C z))
          (0, 1) p := congrArg (fun x => scalarStateOperator D S x (0, 1) p) hy
      _ = _ := (n04Realization_actualLeft_eq_reduced hT hS h01 h03
        hraw hsector hg hp).symm
  · rw [scalarHeight_decode_eq_zero_outside hS _ hp]
    obtain ⟨J, _, hJD, _, hzero⟩ := n06_currentLeftColumns_commonSupport (L := L) hS
    exact (hzero (liftSectorParameter S C z) p.1
      (fun hpJ => hp ⟨hJD hpJ, mem_univ _⟩) p.2).symm

end ContinuousFlexibility.Analysis
