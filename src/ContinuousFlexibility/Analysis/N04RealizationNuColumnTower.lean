import ContinuousFlexibility.Analysis.N04RealizationNuReducedTower
import ContinuousFlexibility.Analysis.N04RealizationUniformAffine
import ContinuousFlexibility.Analysis.N04RealizationUniformSector
import ContinuousFlexibility.Analysis.N07aNuSource

/-!
# The true distinguished column with its uniform sector tower

The actual reduced scalar column is pulled back along the prescribed
affine sector projection. One smaller sector neighborhood carries its
entire height-valued tower and the exact original physical decoder.
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

/-- The physical nu column has a genuine height-valued tower with one
fixed neighborhood and loss. Its output is not an arbitrary witness:
the decoder is the actual column at every physical point. -/
theorem n04Realization_exists_uniformNuColumn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) :
    ∃ b ell : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      ∃ N : (StateDirections S × ℝ) → ScalarHeightSpace S,
        FixedNeighborhoodSmoothTame (n07aParameterGrading S) (scalarHeightGrading S)
          (sectorNeighborhood S b η η) b ell N ∧
        (∀ z ∈ sectorNeighborhood S b η η, ∀ p,
          (S.height scalarBeta).decode (N z) p =
            nuColumnField D S C (liftSectorParameter S C z) p) := by
  letI : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  have hseed :=
    n04Realization_exists_uniformNuReducedColumn h01.1.1 hT hS h01.1.2.2.2.1
      C.referenceState.1.1
  let U : Set (N07aNuParameter S) := hseed.choose
  have hU : IsOpen U := hseed.choose_spec.1
  have hcenter : n07aNuParameterCenter S C.referenceState.1.1 ∈ U :=
    hseed.choose_spec.2.1
  let b₀ : ℕ := hseed.choose_spec.2.2.choose
  let ell : ℕ := hseed.choose_spec.2.2.choose_spec.choose
  let N : N07aNuParameter S → ScalarHeightSpace S :=
    hseed.choose_spec.2.2.choose_spec.choose_spec.choose
  have hN : FixedNeighborhoodSmoothTame (n07aNuParameterGrading S)
      (scalarHeightGrading S) U b₀ ell N :=
    hseed.choose_spec.2.2.choose_spec.choose_spec.choose_spec.1
  have hdecode := hseed.choose_spec.2.2.choose_spec.choose_spec.choose_spec.2
  let c : N07aNuParameter S := n07aNuParameterCenter S C.referenceState.1.1
  let A : (StateDirections S × ℝ) → N07aNuParameter S :=
    fun z => c + n07aNuSectorProjectionCLM S z
  have hA : Continuous A := continuous_const.add (n07aNuSectorProjectionCLM S).continuous
  have hA0 : A (0 : StateDirections S × ℝ) = c :=
    (congrArg (fun y : N07aNuParameter S => c + y)
      (map_zero (n07aNuSectorProjectionCLM S))).trans (add_zero c)
  have hzero : (0 : StateDirections S × ℝ) ∈ A ⁻¹' U := by
    rw [Set.mem_preimage, hA0]
    exact hcenter
  have hpull : FixedNeighborhoodSmoothTame (n07aParameterGrading S)
      (scalarHeightGrading S) (A ⁻¹' U) b₀ ell (fun z => N (A z)) :=
    n04Realization_fixedNeighborhood_affine hN c (n07aNuSectorProjectionCLM S)
      (n07aNuSectorProjectionCLM_grading_le S)
  obtain ⟨b, η, hb, hη, hηε, hmaps, htower⟩ :=
    n04Realization_fixedNeighborhood_sectorRestriction S (base := base)
      (hU.preimage hA) hzero hpull h01.2.1
  refine ⟨b, ell, η, hb, hη, hηε, fun z => N (A z), htower, ?_⟩
  intro z hz p
  have hcoord : A z = n07aNuRawProjectionCLM S (liftSectorParameter S C z) :=
    n07aNuSectorProjectionCLM_center h01.2.2.1 z
  apply (hdecode (A z) (hmaps hz) p).trans
  rw [hcoord]
  exact (n07a_nuColumnField_eq_pureResidual_deriv hS hT h01
    (liftSectorParameter S C z) p).symm

end ContinuousFlexibility.Analysis
