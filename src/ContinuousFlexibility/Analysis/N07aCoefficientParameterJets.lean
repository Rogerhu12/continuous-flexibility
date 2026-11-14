module

public import ContinuousFlexibility.Analysis.N07aAffineTower
public import ContinuousFlexibility.Analysis.N07aCoefficientFields
public import ContinuousFlexibility.Analysis.N07aProfileParameterJets
public import ContinuousFlexibility.Analysis.N07aParameterGrading

/-!
# Genuine coefficient towers on the actual affine sector

The tangent inclusion preserves every sum seminorm exactly. Pulling the
N01 towers along the original affine sector map therefore keeps their
physical decay, base order, and derivative loss unchanged.
-/

@[expose] public section

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

local instance n07aCoefficientParameterRawTopGroup (S : PhysicalSpacesData) :
    IsTopologicalAddGroup (AnnularState S × ℝ) :=
  (n07aRawParameterGrading_withSeminorms S).isTopologicalAddGroup

/-- The actual tangent inclusion into the raw annular parameter space. -/
def n07aSectorParameterInclusion (S : PhysicalSpacesData) :
    (StateDirections S × ℝ) →L[ℝ] (AnnularState S × ℝ) :=
  (stateSectorSubmodule S).subtypeL.prodMap (ContinuousLinearMap.id ℝ ℝ)

theorem n07aSectorParameterInclusion_apply (S : PhysicalSpacesData)
    (z : StateDirections S × ℝ) : n07aSectorParameterInclusion S z = (z.1.val, z.2) := by
  simp only [n07aSectorParameterInclusion, ContinuousLinearMap.coe_prodMap',
    Prod.map_apply', Submodule.subtypeL_apply, ContinuousLinearMap.id_apply]

theorem n07aSectorParameterInclusion_grading (S : PhysicalSpacesData) (n : ℕ)
    (z : StateDirections S × ℝ) :
    n07aRawParameterGrading S n (n07aSectorParameterInclusion S z) =
      n07aParameterGrading S n z := by
  simp only [n07aRawParameterGrading_apply, n07aRawParameterSize,
    n07aSectorParameterInclusion_apply, n07aParameterGrading, pairGrading_apply,
    sectorGrading, Seminorm.comp_apply, Submodule.subtype_apply, realGrading,
    coe_normSeminorm, Real.norm_eq_abs]

theorem n07aSectorParameterInclusion_lift (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ) :
    (C.referenceState, 0) + n07aSectorParameterInclusion S z = liftSectorParameter S C z := by
  simp only [n07aSectorParameterInclusion_apply, Prod.mk_add_mk, zero_add, liftSectorParameter]

theorem n07aSectorParameterInclusion_lift_sub (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ) :
    liftSectorParameter S C z - (C.referenceState, 0) = n07aSectorParameterInclusion S z := by
  calc
    _ = ((C.referenceState, 0) + n07aSectorParameterInclusion S z) -
        (C.referenceState, 0) :=
      congrArg (fun t : AnnularState S × ℝ => t - (C.referenceState, 0))
        (n07aSectorParameterInclusion_lift S C z).symm
    _ = _ := add_sub_cancel_left _ _

theorem n07aSectorParameterVariation_eq (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base high : ℕ) (z : StateDirections S × ℝ)
    {k : ℕ} (v : Fin k → (StateDirections S × ℝ)) :
    n07aRawParameterVariation S base high (liftSectorParameter S C z - (C.referenceState, 0))
      (fun i => n07aSectorParameterInclusion S (v i)) =
        oneHighVariationWeight (n07aParameterGrading S) base high z v := by
  simp only [n07aRawParameterVariation, n07aSectorParameterInclusion_lift_sub,
    ← n07aRawParameterGrading_apply, n07aSectorParameterInclusion_grading,
    oneHighVariationWeight]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The chosen N01 tower, pulled back to the original affine sector. -/
def n07aCoefficientParameterJet
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (i : Fin 3) (a b : ℕ) (p : annularOpen D) :
    SmoothDirections (E := StateDirections S × ℝ) (F := ℝ)
      (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative a b
        (n07aCoefficientDifferenceField D S C i (liftSectorParameter S C z)) p.val) :=
  (smoothDirectionsRestrict
    (n07aSmoothDirectionsAffine (n07aCoefficientTower hT h01 i a b p)
      (C.referenceState, 0) (n07aSectorParameterInclusion S))
    (n07a_sectorNeighborhood_isOpen S base ε ε) (fun z hz => by
      rw [Set.mem_preimage, n07aSectorParameterInclusion_lift]
      exact liftSectorParameter_mem_stateNeighborhood hz le_rfl)).congr
    (fun z _ => by
      rw [n07aSectorParameterInclusion_lift]
      exact (n07aCoefficientDifferenceField_mixedDerivative i _ a b p.property).symm)

theorem n07aCoefficientParameterJet_D
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (i : Fin 3) (a b : ℕ) (p : annularOpen D) (k : ℕ)
    (z : StateDirections S × ℝ) (v : Fin k → (StateDirections S × ℝ)) :
    (n07aCoefficientParameterJet hT h01 i a b p).D k z v =
      (n07aCoefficientTower hT h01 i a b p).D k (liftSectorParameter S C z)
        (fun j => n07aSectorParameterInclusion S (v j)) := by
  simp only [n07aCoefficientParameterJet, SmoothDirections.congr, smoothDirectionsRestrict,
    n07aSmoothDirectionsAffine, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    n07aSectorParameterInclusion_lift]

private theorem n07a_parameter_jet_bound_transport {a b M V W : ℝ}
    (hab : a = b) (hVW : V = W) (hb : |b| ≤ M * V) : |a| ≤ M * W := by
  rw [hab, ← hVW]
  exact hb

theorem n07aCoefficientParameterJet_decay_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (i : Fin 3) (a b : ℕ) (p : annularOpen D), a + b ≤ s →
      ∀ z : StateDirections S × ℝ, z ∈ sectorNeighborhood S base ε ε →
      ∀ v : Fin k → (StateDirections S × ℝ),
        |(n07aCoefficientParameterJet hT h01 i a b p).D k z v| ≤
          B * T.H p.val.1 ^ (3 / 64 : ℝ) *
            oneHighVariationWeight (n07aParameterGrading S) base (s + loss) z v := by
  let data := n07aCoefficientTower_decay_bound hT h01 k s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  have hb := data.choose_spec.2
  refine ⟨B, hB, fun i a b p hab z hz v => ?_⟩
  exact n07a_parameter_jet_bound_transport
    (n07aCoefficientParameterJet_D hT h01 i a b p k z v)
    (n07aSectorParameterVariation_eq S C base (s + loss) z v)
    (hb i a b p hab (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (fun j => n07aSectorParameterInclusion S (v j)))

end ContinuousFlexibility.Analysis
