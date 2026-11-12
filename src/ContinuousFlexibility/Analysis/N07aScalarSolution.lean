import ContinuousFlexibility.Analysis.N07aCorrectedForward
import ContinuousFlexibility.Analysis.N07aNormalizedSpaces
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# The actual normalized scalar equation is a linear solution relation

The coefficient part is the already constructed physical forward map.
The distinguished column is used only as its literal pointwise field;
no Source realization or parameter regularity of that column is needed.
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

/-- The same equation and row appearing in `ScalarLinearInverseProperties`. -/
def N07aScalarSolution (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (f : S.Source) (u : HeightPair S × ℝ) : Prop :=
  referenceRow D (heightPairField S u.1) = 0 ∧
    ∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients z) (heightPairField S u.1) p +
        u.2 * nuColumnField D S C z p = (S.height (3 / 4 : ℝ)).decode f.val p

/-- The actual inverse of translation by the reference state on the sector. -/
def n07aSectorParameterOfState
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (z : AnnularState S × ℝ)
    (hs : stateSector S z.1) : StateDirections S × ℝ :=
  (⟨z.1 - C.referenceState,
    (stateSectorSubmodule S).sub_mem hs href.stateSector⟩, z.2)

theorem lift_n07aSectorParameterOfState
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (z : AnnularState S × ℝ)
    (hs : stateSector S z.1) :
    liftSectorParameter S C (n07aSectorParameterOfState href z hs) = z := by
  rcases z with ⟨x, q⟩
  change (C.referenceState + (x - C.referenceState), q) = (x, q)
  congr 1
  abel

theorem n07aSectorParameterOfState_mem
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) {base : ℕ} {ε : ℝ}
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    n07aSectorParameterOfState href z hs ∈ sectorNeighborhood S base ε ε := by
  exact hz

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

/-- The actual scalar equation as a linear field, before Source restriction. -/
def n07aScalarCoreOperator
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε) (z : StateDirections S × ℝ) :
    (HeightPair S × ℝ) →ₗ[ℝ] (PolarPoint → ℝ) :=
  ((((S.height (3 / 4 : ℝ)).decode.comp S.Q.toLinearMap.ker.subtype).comp
    (n07aCorrectedForwardCLM hS hT h01 h02 h03 z).toLinearMap).comp
      (LinearMap.fst ℝ (HeightPair S) ℝ)) +
    (LinearMap.snd ℝ (HeightPair S) ℝ).smulRight
      (nuColumnField D S C (liftSectorParameter S C z))

theorem n07aScalarCoreOperator_apply
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (z : StateDirections S × ℝ) (u : HeightPair S × ℝ) (p : PolarPoint) :
    n07aScalarCoreOperator hS hT h01 h02 h03 z u p =
      (S.height (3 / 4 : ℝ)).decode
        (n07aCorrectedForwardCLM hS hT h01 h02 h03 z u.1).val p +
        u.2 * nuColumnField D S C (liftSectorParameter S C z) p := by
  simp only [n07aScalarCoreOperator, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply,
    ContinuousLinearMap.coe_coe, LinearMap.smulRight_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]

theorem n07aScalarCoreOperator_decode
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S × ℝ) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    n07aScalarCoreOperator hS hT h01 h02 h03 z u p =
      divergenceOperator (L.coefficients (liftSectorParameter S C z))
        (heightPairField S u.1) p +
        u.2 * nuColumnField D S C (liftSectorParameter S C z) p := by
  rw [n07aScalarCoreOperator_apply,
    n07aCorrectedForwardCLM_decode hS hT h01 h02 h03 hz u.1 hp]

theorem n07aScalarSolution_add
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f g : S.Source} {u v : HeightPair S × ℝ}
    (hu : N07aScalarSolution D S C L z f u)
    (hv : N07aScalarSolution D S C L z g v) :
    N07aScalarSolution D S C L z (f + g) (u + v) := by
  let ζ := n07aSectorParameterOfState h01.2.2.1 z hs
  let O := n07aScalarCoreOperator hS hT h01 h02 h03 ζ
  have he (a : HeightPair S × ℝ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
      O a p = divergenceOperator (L.coefficients z) (heightPairField S a.1) p +
        a.2 * nuColumnField D S C z p := by
    simpa only [lift_n07aSectorParameterOfState] using
      n07aScalarCoreOperator_decode hS hT h01 h02 h03
        (n07aSectorParameterOfState_mem h01.2.2.1 hz hs) a hp
  let rowMap : (HeightPair S × ℝ) →L[ℝ] ℝ := n07aNormalizationRow h01.1 hT hS
  have hRu : rowMap u = 0 := (n07aNormalizationRow_apply h01.1 hT hS u).trans hu.1
  have hRv : rowMap v = 0 := (n07aNormalizationRow_apply h01.1 hT hS v).trans hv.1
  constructor
  · exact (n07aNormalizationRow_apply h01.1 hT hS (u + v)).symm.trans
      ((map_add rowMap u v).trans
        ((congrArg₂ (fun a b : ℝ => a + b) hRu hRv).trans (add_zero 0)))
  · intro p hp
    apply (he (u + v) p hp).symm.trans
    calc
      O (u + v) p = O u p + O v p :=
        congrArg (fun F : PolarPoint → ℝ => F p) (map_add O u v)
      _ = (S.height (3 / 4 : ℝ)).decode f.val p +
          (S.height (3 / 4 : ℝ)).decode g.val p :=
        congrArg₂ (fun a b : ℝ => a + b) ((he u p hp).trans (hu.2 p hp))
          ((he v p hp).trans (hv.2 p hp))
      _ = _ := by simp only [Submodule.coe_add, map_add, Pi.add_apply]

theorem n07aScalarSolution_smul
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : S.Source} {u : HeightPair S × ℝ}
    (hu : N07aScalarSolution D S C L z f u) (c : ℝ) :
    N07aScalarSolution D S C L z (c • f) (c • u) := by
  let ζ := n07aSectorParameterOfState h01.2.2.1 z hs
  let O := n07aScalarCoreOperator hS hT h01 h02 h03 ζ
  have he (a : HeightPair S × ℝ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
      O a p = divergenceOperator (L.coefficients z) (heightPairField S a.1) p +
        a.2 * nuColumnField D S C z p := by
    simpa only [lift_n07aSectorParameterOfState] using
      n07aScalarCoreOperator_decode hS hT h01 h02 h03
        (n07aSectorParameterOfState_mem h01.2.2.1 hz hs) a hp
  let rowMap : (HeightPair S × ℝ) →L[ℝ] ℝ := n07aNormalizationRow h01.1 hT hS
  have hRu : rowMap u = 0 := (n07aNormalizationRow_apply h01.1 hT hS u).trans hu.1
  constructor
  · exact (n07aNormalizationRow_apply h01.1 hT hS (c • u)).symm.trans
      ((map_smul rowMap c u).trans
        ((congrArg (fun a : ℝ => c • a) hRu).trans (smul_zero c)))
  · intro p hp
    apply (he (c • u) p hp).symm.trans
    calc
      O (c • u) p = c * O u p := by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          congrArg (fun F : PolarPoint → ℝ => F p) (map_smul O c u)
      _ = c * (S.height (3 / 4 : ℝ)).decode f.val p :=
        congrArg (fun a : ℝ => c * a) ((he u p hp).trans (hu.2 p hp))
      _ = _ := by simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]

end ContinuousFlexibility.Analysis
