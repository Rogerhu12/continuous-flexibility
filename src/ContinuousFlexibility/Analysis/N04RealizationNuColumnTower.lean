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
  obtain ⟨U, hU, hcenter, b₀, ell, N, hN, hdecode⟩ :=
    n04Realization_exists_uniformNuReducedColumn h01.1.1 hT hS h01.1.2.2.2.1
      C.referenceState.1.1
  let c : N07aNuParameter S := n07aNuParameterCenter S C.referenceState.1.1
  let A : (StateDirections S × ℝ) → N07aNuParameter S :=
    fun z => c + n07aNuSectorProjectionCLM S z
  have hA : Continuous A := continuous_const.add (n07aNuSectorProjectionCLM S).continuous
  have hA0 : A (0 : StateDirections S × ℝ) = c := by
    simp only [A, map_zero, add_zero]
  have hzero : (0 : StateDirections S × ℝ) ∈ A ⁻¹' U := by
    exact hA0.symm ▸ hcenter
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
