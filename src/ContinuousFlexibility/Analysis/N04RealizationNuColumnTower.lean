import ContinuousFlexibility.Analysis.N04RealizationNuReducedTower
import ContinuousFlexibility.Analysis.N04RealizationUniformAffineFamily
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

private theorem n04Realization_nuColumn_affineDecoder
    {X Y Z P : Type*} {U : Set Y} {V : Set X}
    (decode : Z → P → ℝ) (N : Y → Z) (F : Y → P → ℝ)
    (A B : X → Y) (field : X → P → ℝ)
    (hdecode : ∀ y ∈ U, ∀ p, decode (N y) p = F y p)
    (hmaps : MapsTo A V U)
    (hcoord : ∀ x, A x = B x)
    (hfield : ∀ x p, field x p = F (B x) p) :
    ∀ x ∈ V, ∀ p, decode (N (A x)) p = field x p := by
  intro x hx p
  exact (hdecode (A x) (hmaps hx) p).trans
    ((congrArg (fun y : Y => F y p) (hcoord x)).trans (hfield x p).symm)

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
  exact n04Realization_uniformAffine_family
    (X := StateDirections S × ℝ) (Y := N07aNuParameter S) (Z := ScalarHeightSpace S)
    (n07aParameterGrading S) (n07aNuParameterGrading S) (scalarHeightGrading S)
    (n07aNuParameterCenter S C.referenceState.1.1) (n07aNuSectorProjectionCLM S)
    (n07aNuSectorProjectionCLM_grading_le S)
    (fun b η => sectorNeighborhood S b η η) base ε
    (fun U N => ∀ y ∈ U, ∀ p, (S.height scalarBeta).decode (N y) p =
      deriv (fun ν => scalarStateResidual D S
        (n07aNuParameterState hT hS h01.1.2.2.2.1 ((y.1.1, ν), y.2)) p) y.1.2)
    (fun b η N => ∀ z ∈ sectorNeighborhood S b η η, ∀ p,
      (S.height scalarBeta).decode (N z) p =
        nuColumnField D S C (liftSectorParameter S C z) p)
    (fun W f b ell hW hzero hf =>
      n04Realization_fixedNeighborhood_sectorRestriction S (base := base)
        (towerBase := b) (loss := ell) (f := f) hW hzero hf h01.2.1)
    (fun U N hdecode b η _ _ _ hmaps =>
      n04Realization_nuColumn_affineDecoder
        (U := U) (V := sectorNeighborhood S b η η)
        (S.height scalarBeta).decode N
        (fun y p => deriv (fun ν => scalarStateResidual D S
          (n07aNuParameterState hT hS h01.1.2.2.2.1 ((y.1.1, ν), y.2)) p) y.1.2)
        (fun z => n07aNuParameterCenter S C.referenceState.1.1 +
          n07aNuSectorProjectionCLM S z)
        (fun z => n07aNuRawProjectionCLM S (liftSectorParameter S C z))
        (fun z => nuColumnField D S C (liftSectorParameter S C z))
        hdecode hmaps (n07aNuSectorProjectionCLM_center h01.2.2.1)
        (fun z p => by
          simpa only [n07aNuRawProjectionCLM_apply,
            n07aNuParameterState, n07aNuScalarState] using
            n07a_nuColumnField_eq_pureResidual_deriv hS hT h01
              (liftSectorParameter S C z) p))
    (n04Realization_exists_uniformNuReducedColumn h01.1.1 hT hS
      h01.1.2.2.2.1 C.referenceState.1.1)

end ContinuousFlexibility.Analysis
