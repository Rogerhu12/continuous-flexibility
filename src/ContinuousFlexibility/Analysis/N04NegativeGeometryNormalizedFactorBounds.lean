module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryRootProfileJoint
public import ContinuousFlexibility.Analysis.N04NegativeGeometryMixedPowerTransfer
public import ContinuousFlexibility.Analysis.N01cNormalizedSpeedPowerBounds
public import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection

/-!
# Fixed-base bounds for the actual normalized root factors

The proved N01 controlled fields already contain the rational drift and
the optical speed multiplier. One interpolation base is chosen before
every spatial and parameter order. The sector inclusion preserves the
grading, so both actual factors retain the original full height gain.
The bounds hold on the whole annulus and do not contain a collar radius.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private abbrev factorStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] factorStateTopology
private abbrev factorStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] factorStateGroup
private abbrev factorStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] factorStateModule
private abbrev factorStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (factorStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] factorStateSMul

private theorem normalizedFactor_partA
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) : N01PartA D T S C :=
  ⟨hN.1, hN.2.2.1, hN.2.2.2.1, hN.2.2.2.2.1, hN.2.2.2.2.2.1⟩

private theorem normalizedFactor_partB
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) : N01PartB D S C base ε :=
  ⟨hN.2.2.2.2.2.2.1, hN.2.2.2.2.2.2.2.1,
    hN.2.2.2.2.2.2.2.2.1, hN.2.2.2.2.2.2.2.2.2.1,
    hN.2.2.2.2.2.2.2.2.2.2.1⟩

private theorem controlledField_regular_bounds
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}
    (F : PowerControlledField p center base loss U Ω H E)
    (f : X → PolarPoint → ℝ) (he : F.value = f) :
    ∃ J : MixedJetRegularity U Ω f, MixedPowerBounds p center base loss U Ω H E f := by
  subst f
  exact ⟨F.regular, F.bounds⟩

/-- The controlled N01 family is unpacked while all physical data remain
opaque. This avoids reducing the retained start during tower transport. -/
theorem n04NegativeGeometry_normalizedFactor_regular_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ,
      pairGrading (stateGrading S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading S) realGrading (n + 4) x ≤
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1))) (i : Fin 2) :
    ∃ J : MixedJetRegularity (stateNeighborhood S C base ε) (annularOpen D)
      (normalizedSpeedFactor D S C i),
      MixedPowerBounds (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
        base loss (stateNeighborhood S C base ε) (annularOpen D)
        (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
        (normalizedSpeedFactor D S C i) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  exact controlledField_regular_bounds
    (normalizedSpeedFactor_controlled hS hT hA hε hε1 hB hE hloc hχloc hI i)
    (normalizedSpeedFactor D S C i)
    (normalizedSpeedFactor_controlled_value hS hT hA hε hε1 hB hE hloc hχloc hI i)

private theorem normalizedFactor_sector_regular_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ} {i : Fin 2}
    (RF : MixedJetRegularity (stateNeighborhood S C base ε) (annularOpen D)
      (normalizedSpeedFactor D S C i))
    (hraw : MixedPowerBounds (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
      base loss (stateNeighborhood S C base ε) (annularOpen D)
      (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
      (normalizedSpeedFactor D S C i)) :
    ∃ J : MixedJetRegularity (sectorNeighborhood S base ε ε) (annularOpen D)
      (fun z => normalizedSpeedFactor D S C i (liftSectorParameter S C z)),
      MixedPowerBounds (pairGrading (sectorGrading S) realGrading) 0 base loss
        (sectorNeighborhood S base ε ε) (annularOpen D)
        (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
        (fun z => normalizedSpeedFactor D S C i (liftSectorParameter S C z)) := by
  have hmap : MapsTo (fun z : StateDirections S × ℝ =>
      (C.referenceState, 0) + sectorParameterInclusion S z)
      (sectorNeighborhood S base ε ε) (stateNeighborhood S C base ε) := by
    intro z hz
    change (C.referenceState, 0) + sectorParameterInclusion S z ∈ _
    rw [← liftSectorParameter_eq_affine S C z]
    exact liftSectorParameter_mem_stateNeighborhood hz le_rfl
  exact n04NegativeGeometry_mixedPower_affine_domain
    (sectorParameterInclusion S) (C.referenceState, 0)
    (sectorNeighborhood_isOpen S base ε ε) (isOpen_Ioo.prod isOpen_univ) (Subset.refl _)
    hmap (pairGrading_sectorParameterInclusion S) RF hraw
    (fun z hz p hp => congrArg (fun x => normalizedSpeedFactor D S C i x p)
      (liftSectorParameter_eq_affine S C z))

private theorem normalizedFactorSector_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {oldBase oldLoss base loss : ℕ} {oldε ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C oldBase oldLoss oldε)
    (hb : oldBase ≤ base) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεold : ε ≤ oldε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ,
      pairGrading (stateGrading S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading S) realGrading (n + 4) x ≤
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1))) :
    ∀ i : Fin 2, ∃ J : MixedJetRegularity (sectorNeighborhood S base ε ε) (annularOpen D)
      (fun z => normalizedSpeedFactor D S C i (liftSectorParameter S C z)),
      MixedPowerBounds (pairGrading (sectorGrading S) realGrading) 0 base loss
        (sectorNeighborhood S base ε ε) (annularOpen D)
        (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
        (fun z => normalizedSpeedFactor D S C i (liftSectorParameter S C z)) := by
  intro i
  refine (n04NegativeGeometry_normalizedFactor_regular_bounds
    hS hT (normalizedFactor_partA hN) hε hε1
    (n01PartB_mono (normalizedFactor_partB hN) hb hεold) hE hloc hχloc hI i).elim ?_
  intro RF hraw
  exact normalizedFactor_sector_regular_bounds RF hraw

namespace N04RealizationStart

variable (W : N04RealizationStart)

def NegativeNormalizedFactorPowerBounds (base loss : ℕ) : Prop :=
  ∀ i : Fin 2, ∃ J : MixedJetRegularity
      (sectorNeighborhood W.S base W.negativeRootParameterRadius W.negativeRootParameterRadius)
      (annularOpen W.D)
      (fun z => normalizedSpeedFactor W.D W.S W.C i (liftSectorParameter W.S W.C z)),
    MixedPowerBounds (pairGrading (sectorGrading W.S) realGrading) 0 base loss
      (sectorNeighborhood W.S base W.negativeRootParameterRadius W.negativeRootParameterRadius)
      (annularOpen W.D) (fun p => W.T.H p.1 ^ (3 / 4 : ℝ)) (fun p => W.T.E0 p.1)
      (fun z => normalizedSpeedFactor W.D W.S W.C i (liftSectorParameter W.S W.C z))

private theorem negativeNormalizedFactor_of_interpolation
    (base loss : ℕ) (hb : W.base ≤ base)
    (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState W.S × ℝ,
      pairGrading (stateGrading W.S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading W.S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading W.S) realGrading (n + 4) x ≤
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1))) :
    W.NegativeNormalizedFactorPowerBounds base loss :=
  normalizedFactorSector_of_n01 W.hS W.hT W.through03.1.1 hb
    W.negativeRootParameterRadius_pos
    ((min_le_right W.ε (1 / 2 : ℝ)).trans (by norm_num)) (min_le_left _ _)
    (fun r _ => W.floor r) W.primitive.1 W.primitive.2.1 hI

/-- The retained start supplies all inputs to the existing N01 theorem.
In particular, neither an estimate nor a derivative tower of a target
chart or root flow is assumed. -/
theorem negativeNormalizedFactor_mixedPowerBounds :
    ∃ base loss : ℕ, W.base ≤ base ∧ W.NegativeNormalizedFactorPowerBounds base loss :=
  exists_base_ge_of_spatialPower_continuation
    (pairGrading (stateGrading W.S) realGrading) (jointStateGrading_monotone W.S)
    (jointStateGrading_hasInterpolation W.hS) W.base 4
    (fun base loss => W.NegativeNormalizedFactorPowerBounds base loss)
    (W.negativeNormalizedFactor_of_interpolation)

end N04RealizationStart

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeNormalizedFactor_mixedPowerBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeNormalizedFactor_mixedPowerBounds
