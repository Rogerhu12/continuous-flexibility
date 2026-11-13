import ContinuousFlexibility.Analysis.N04NegativeGeometryRootProfileJoint
import ContinuousFlexibility.Analysis.N04NegativeGeometryMixedPowerTransfer
import ContinuousFlexibility.Analysis.N01cNormalizedSpeedPowerBounds
import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection
import ContinuousFlexibility.Analysis.N07aNeighborhood

/-!
# Fixed-base bounds for the actual normalized root factors

The proved N01 controlled fields already contain the rational drift and
the optical speed multiplier. One interpolation base is chosen before
every spatial and parameter order. The sector inclusion preserves the
grading, so both actual factors retain the original full height gain.
The bounds hold on the whole annulus and do not contain a collar radius.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

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
  let F := normalizedSpeedFactor_controlled hS hT hA hε hε1 hB hE hloc hχloc hI i
  have hF : F.value = normalizedSpeedFactor D S C i :=
    normalizedSpeedFactor_controlled_value hS hT hA hε hε1 hB hE hloc hχloc hI i
  have RF := F.regular
  have hb := F.bounds
  rw [hF] at RF hb
  exact ⟨RF, hb⟩

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
    W.NegativeNormalizedFactorPowerBounds base loss := by
  have h01 := W.through03.1.1
  have hA : N01PartA W.D W.T W.S W.C :=
    ⟨h01.1, h01.2.2.1, h01.2.2.2.1, h01.2.2.2.2.1, h01.2.2.2.2.2.1⟩
  have hB : N01PartB W.D W.S W.C W.base W.ε :=
    ⟨h01.2.2.2.2.2.2.1, h01.2.2.2.2.2.2.2.1,
      h01.2.2.2.2.2.2.2.2.1, h01.2.2.2.2.2.2.2.2.2.1,
      h01.2.2.2.2.2.2.2.2.2.2.1⟩
  have hB' : N01PartB W.D W.S W.C base W.negativeRootParameterRadius :=
    n01PartB_mono hB hb (min_le_left _ _)
  intro i
  obtain ⟨RF, hraw⟩ := n04NegativeGeometry_normalizedFactor_regular_bounds
    (D := W.D) (T := W.T) (S := W.S) (C := W.C) W.hS W.hT hA
    W.negativeRootParameterRadius_pos
    ((min_le_right W.ε (1 / 2 : ℝ)).trans (by norm_num)) hB'
    (fun r _ => W.floor r) W.primitive.1 W.primitive.2.1 hI i
  have hmap : MapsTo (fun z : StateDirections W.S × ℝ =>
      (W.C.referenceState, 0) + sectorParameterInclusion W.S z)
      (sectorNeighborhood W.S base W.negativeRootParameterRadius
        W.negativeRootParameterRadius)
      (stateNeighborhood W.S W.C base W.negativeRootParameterRadius) := by
    intro z hz
    change (W.C.referenceState, 0) + sectorParameterInclusion W.S z ∈ _
    rw [← liftSectorParameter_eq_affine W.S W.C z]
    exact liftSectorParameter_mem_stateNeighborhood hz le_rfl
  exact n04NegativeGeometry_mixedPower_affine_domain
    (sectorParameterInclusion W.S) (W.C.referenceState, 0)
    (sectorNeighborhood_isOpen W.S base W.negativeRootParameterRadius
      W.negativeRootParameterRadius) (isOpen_Ioo.prod isOpen_univ) (Subset.refl _)
    hmap (pairGrading_sectorParameterInclusion W.S) RF hraw
    (fun z hz p hp => congrArg
      (fun x => normalizedSpeedFactor W.D W.S W.C i x p)
      (liftSectorParameter_eq_affine W.S W.C z))

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
