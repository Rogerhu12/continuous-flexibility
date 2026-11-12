import ContinuousFlexibility.Analysis.N07aNuReducedSource
import ContinuousFlexibility.Analysis.N07aNuScalarState
import ContinuousFlexibility.Analysis.N07aAffineTame
import ContinuousFlexibility.Analysis.N07aCoefficientParameterJets

/-!
# The true distinguished column is a smooth tame Source family

The reduced border state is the actual affine projection of the annular
state. Its open realization domain contains the reference point. One
smaller sector neighborhood therefore carries the original distinguished
column as a genuine Source-valued smooth tame family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

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

def n07aNuRawProjectionCLM (S : PhysicalSpacesData) :
    (AnnularState S × ℝ) →L[ℝ] N07aNuParameter S where
  toFun z := ((z.1.1, z.1.2.1), z.2)
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl
  cont := (continuous_fst.fst.prodMk continuous_fst.snd.fst).prodMk continuous_snd

theorem n07aNuRawProjectionCLM_apply (S : PhysicalSpacesData) (z : AnnularState S × ℝ) :
    n07aNuRawProjectionCLM S z = ((z.1.1, z.1.2.1), z.2) := rfl

def n07aNuSectorProjectionCLM (S : PhysicalSpacesData) :
    (StateDirections S × ℝ) →L[ℝ] N07aNuParameter S :=
  (n07aNuRawProjectionCLM S).comp (n07aSectorParameterInclusion S)

theorem n07aNuSectorProjectionCLM_apply (S : PhysicalSpacesData)
    (z : StateDirections S × ℝ) :
    n07aNuSectorProjectionCLM S z = ((z.1.val.1, z.1.val.2.1), z.2) := by
  have hc : n07aNuSectorProjectionCLM S z =
      n07aNuRawProjectionCLM S (n07aSectorParameterInclusion S z) :=
    ContinuousLinearMap.comp_apply (n07aNuRawProjectionCLM S)
      (n07aSectorParameterInclusion S) z
  have hi : n07aNuRawProjectionCLM S (n07aSectorParameterInclusion S z) =
      n07aNuRawProjectionCLM S (z.1.val, z.2) :=
    congrArg (fun x : AnnularState S × ℝ => n07aNuRawProjectionCLM S x)
      (n07aSectorParameterInclusion_apply S z)
  exact hc.trans (hi.trans (n07aNuRawProjectionCLM_apply S (z.1.val, z.2)))

private theorem n07aNuSectorProjectionCLM_zero (S : PhysicalSpacesData) :
    n07aNuSectorProjectionCLM S (0 : StateDirections S × ℝ) =
      (0 : N07aNuParameter S) := by
  simp only [n07aNuSectorProjectionCLM_apply, Prod.fst_zero, Prod.snd_zero,
    Submodule.coe_zero, Prod.mk_zero_zero]

theorem n07aNuSectorProjectionCLM_grading_le (S : PhysicalSpacesData) (n : ℕ)
    (z : StateDirections S × ℝ) :
    n07aNuParameterGrading S n (n07aNuSectorProjectionCLM S z) ≤
      n07aParameterGrading S n z := by
  let height : ℝ := heightPairGrading S n z.1.val.1
  let nu : ℝ := realGrading n z.1.val.2.1
  let outer : ℝ := realGrading n z.2
  let controls : ℝ := pairGrading (S.circle (3 / 4 : ℝ)).grading
    (S.circle (3 / 4 : ℝ)).grading n z.1.val.2.2
  have hcommon : scalarCommonHeightGrading S n z.1.val.1 = height := by
    simp only [height, scalarCommonHeightGrading, scalarHeightGrading,
      scalarBeta, heightPairGrading, pairGrading_apply]
    exact pairGrading_apply (E := (S.height (3 / 4 : ℝ)).Space) (F := ℝ)
      (S.height (3 / 4 : ℝ)).grading realGrading n z.1.val.1
  have hinner : pairGrading (scalarCommonHeightGrading S) realGrading n
      (z.1.val.1, z.1.val.2.1) = height + nu :=
    (pairGrading_apply (scalarCommonHeightGrading S) realGrading n
      (z.1.val.1, z.1.val.2.1)).trans
        (congrArg (fun t : ℝ => t + nu) hcommon)
  have hprojection : n07aNuParameterGrading S n (n07aNuSectorProjectionCLM S z) =
      (height + nu) + outer := by
    calc
      n07aNuParameterGrading S n (n07aNuSectorProjectionCLM S z) =
          n07aNuParameterGrading S n ((z.1.val.1, z.1.val.2.1), z.2) :=
        congrArg (fun x : N07aNuParameter S => n07aNuParameterGrading S n x)
          (n07aNuSectorProjectionCLM_apply S z)
      _ = pairGrading (scalarCommonHeightGrading S) realGrading n
          (z.1.val.1, z.1.val.2.1) + outer :=
        pairGrading_apply (pairGrading (scalarCommonHeightGrading S) realGrading)
          realGrading n ((z.1.val.1, z.1.val.2.1), z.2)
      _ = (height + nu) + outer := congrArg (fun t : ℝ => t + outer) hinner
  have hcontrols : pairGrading realGrading
      (pairGrading (S.circle (3 / 4 : ℝ)).grading
        (S.circle (3 / 4 : ℝ)).grading) n z.1.val.2 = nu + controls :=
    pairGrading_apply realGrading
      (pairGrading (S.circle (3 / 4 : ℝ)).grading
        (S.circle (3 / 4 : ℝ)).grading) n z.1.val.2
  have hstate : stateGrading S n z.1.val = height + (nu + controls) :=
    (pairGrading_apply (heightPairGrading S)
      (pairGrading realGrading (pairGrading (S.circle (3 / 4 : ℝ)).grading
        (S.circle (3 / 4 : ℝ)).grading)) n z.1.val).trans
          (congrArg (fun t : ℝ => height + t) hcontrols)
  have hsector : sectorGrading S n z.1 = stateGrading S n z.1.val := by
    simp only [sectorGrading, Seminorm.comp_apply, Submodule.subtype_apply]
  have htarget : n07aParameterGrading S n z =
      (height + (nu + controls)) + outer :=
    (pairGrading_apply (sectorGrading S) realGrading n z).trans
      (congrArg (fun t : ℝ => t + outer) (hsector.trans hstate))
  have hc : 0 ≤ controls := apply_nonneg
    (pairGrading (S.circle (3 / 4 : ℝ)).grading
      (S.circle (3 / 4 : ℝ)).grading n) z.1.val.2.2
  have hnu : nu ≤ nu + controls := le_add_of_nonneg_right hc
  have hnum : (height + nu) + outer ≤ (height + (nu + controls)) + outer :=
    add_le_add (add_le_add (le_refl height) hnu) (le_refl outer)
  exact hprojection.le.trans (hnum.trans htarget.symm.le)

theorem n07aNuSectorProjectionCLM_center
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (z : StateDirections S × ℝ) :
    n07aNuParameterCenter S C.referenceState.1.1 + n07aNuSectorProjectionCLM S z =
      n07aNuRawProjectionCLM S (liftSectorParameter S C z) := by
  have hheight : (C.referenceState.1.1, (0 : ℝ)) = C.referenceState.1 :=
    Prod.ext rfl href.2.1.symm
  simp only [n07aNuParameterCenter, n07aNuSectorProjectionCLM_apply,
    n07aNuRawProjectionCLM_apply, liftSectorParameter, Prod.fst_add, Prod.snd_add,
    Prod.mk_add_mk, href.2.2.1, zero_add]
  exact congrArg
    (fun v : HeightPair S => ((v + z.1.val.1, z.1.val.2.1), z.2)) hheight

private def n07aNuSectorAffine (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S)
    (z : StateDirections S × ℝ) : N07aNuParameter S :=
  n07aNuParameterCenter S v₀ + n07aNuSectorProjectionCLM S z

private theorem n07aNuSectorAffine_continuous
    (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S) :
    Continuous (n07aNuSectorAffine S v₀) := by
  let : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  exact continuous_const.add (n07aNuSectorProjectionCLM S).continuous

private theorem n07aNuSectorAffine_zero
    (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S) :
    n07aNuSectorAffine S v₀ (0 : StateDirections S × ℝ) =
      n07aNuParameterCenter S v₀ :=
  (congrArg (fun x : N07aNuParameter S => n07aNuParameterCenter S v₀ + x)
    (n07aNuSectorProjectionCLM_zero S)).trans (add_zero _)

private theorem n07aNuSectorAffine_smallNeighborhood
    (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S) (base : ℕ)
    {ε : ℝ} (hε : 0 < ε) {U : Set (N07aNuParameter S)} (hU : IsOpen U)
    (hcenter : n07aNuParameterCenter S v₀ ∈ U) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      sectorNeighborhood S base' ε' ε' ⊆ n07aNuSectorAffine S v₀ ⁻¹' U := by
  have hzero : n07aNuSectorAffine S v₀ (0 : StateDirections S × ℝ) ∈ U :=
    Eq.mpr (congrArg (fun x : N07aNuParameter S => x ∈ U)
      (n07aNuSectorAffine_zero S v₀)) hcenter
  have hAU : n07aNuSectorAffine S v₀ ⁻¹' U ∈ 𝓝 (0 : StateDirections S × ℝ) :=
    (hU.preimage (n07aNuSectorAffine_continuous S v₀)).mem_nhds hzero
  let ball := exists_small_uniformTameBall
    (n07aParameterGrading_monotone S) (n07aParameterGrading_withSeminorms S) hAU base
  let base' : ℕ := ball.choose
  let η : ℝ := ball.choose_spec.choose
  have hbase : base ≤ base' := ball.choose_spec.choose_spec.1
  have hη : 0 < η := ball.choose_spec.choose_spec.2.1
  have hsub : {z : StateDirections S × ℝ |
      n07aParameterGrading S base' (z - 0) < η} ⊆
        n07aNuSectorAffine S v₀ ⁻¹' U := ball.choose_spec.choose_spec.2.2.2
  let ε' : ℝ := min ε (η / 2)
  refine ⟨base', hbase, ε', lt_min hε (half_pos hη), min_le_left _ _, ?_⟩
  intro z hz
  apply hsub
  have he : ε' ≤ η / 2 := min_le_right _ _
  have hsize : n07aParameterGrading S base' z =
      sectorGrading S base' z.1 + |z.2| :=
    pairGrading_apply (sectorGrading S) realGrading base' z
  have hbound : sectorGrading S base' z.1 + |z.2| < η := by
    linarith only [hz.1, hz.2, he]
  exact ((congrArg (fun x : StateDirections S × ℝ =>
    n07aParameterGrading S base' x) (sub_zero z)).trans hsize).trans_lt hbound

private theorem n07aNuSectorAffine_smoothTame
    (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S)
    {U : Set (N07aNuParameter S)} {N : N07aNuParameter S → S.Source}
    (hN : SmoothTameOn (n07aNuParameterGrading S) S.sourceGrading U N) :
    SmoothTameOn (n07aParameterGrading S) S.sourceGrading
      (n07aNuSectorAffine S v₀ ⁻¹' U) (N ∘ n07aNuSectorAffine S v₀) := by
  let : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  exact n07a_smoothTameOn_affine_nonexpansive hN
    (n07aNuParameterCenter S v₀) (n07aNuSectorProjectionCLM S)
    (n07aNuSectorProjectionCLM_grading_le S)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem n07aNuSource_reducedDerivative_eq
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (x : N07aNuParameter S) (z : AnnularState S × ℝ)
    (hx : x = n07aNuRawProjectionCLM S z) (p : PolarPoint) :
    deriv (fun ν => scalarStateResidual D S
      (n07aNuParameterState hT hS h01.1.2.2.2.1 ((x.1.1, ν), x.2)) p) x.1.2 =
        nuColumnField D S C z p := by
  let R : N07aNuParameter S → ℝ := fun y => deriv (fun ν => scalarStateResidual D S
    (n07aNuParameterState hT hS h01.1.2.2.2.1 ((y.1.1, ν), y.2)) p) y.1.2
  have he : R x = R (n07aNuRawProjectionCLM S z) := congrArg R hx
  exact he.trans (n07a_nuColumnField_eq_pureResidual_deriv hS hT h01 z p).symm

theorem n07a_exists_nuSource
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∃ N : (StateDirections S × ℝ) → S.Source,
        SmoothTameOn (n07aParameterGrading S) S.sourceGrading
          (sectorNeighborhood S base' ε' ε') N ∧
        (∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ p,
          (S.height (3 / 4 : ℝ)).decode (N z).val p =
            nuColumnField D S C (liftSectorParameter S C z) p) := by
  let data := n07a_exists_nuReducedSource h01.1.1 hT hS h01.1.2.2.2.1
    C.referenceState.1.1
  let U : Set (N07aNuParameter S) := data.choose
  have hU : IsOpen U := data.choose_spec.1
  have hcenter : n07aNuParameterCenter S C.referenceState.1.1 ∈ U := data.choose_spec.2.1
  let N : N07aNuParameter S → S.Source := data.choose_spec.2.2.choose
  have hN : SmoothTameOn (n07aNuParameterGrading S) S.sourceGrading U N :=
    data.choose_spec.2.2.choose_spec.1
  let A : (StateDirections S × ℝ) → N07aNuParameter S :=
    n07aNuSectorAffine S C.referenceState.1.1
  let neighborhood := n07aNuSectorAffine_smallNeighborhood S C.referenceState.1.1
    base h01.2.1 hU hcenter
  let base' : ℕ := neighborhood.choose
  have hbase : base ≤ base' := neighborhood.choose_spec.1
  let ε' : ℝ := neighborhood.choose_spec.2.choose
  have he : 0 < ε' := neighborhood.choose_spec.2.choose_spec.1
  have hle : ε' ≤ ε := neighborhood.choose_spec.2.choose_spec.2.1
  have hmaps : sectorNeighborhood S base' ε' ε' ⊆ A ⁻¹' U :=
    neighborhood.choose_spec.2.choose_spec.2.2
  have hpull : SmoothTameOn (n07aParameterGrading S) S.sourceGrading (A ⁻¹' U) (N ∘ A) :=
    n07aNuSectorAffine_smoothTame S C.referenceState.1.1 hN
  refine ⟨base', hbase, ε', he, hle, N ∘ A,
    smoothTameOn_mono hpull (n07a_sectorNeighborhood_isOpen S base' ε' ε') hmaps, ?_⟩
  intro z hz p
  have hcoord : A z = n07aNuRawProjectionCLM S (liftSectorParameter S C z) :=
    n07aNuSectorProjectionCLM_center h01.2.2.1 z
  have hdecode : (S.height (3 / 4 : ℝ)).decode (N (A z)).val p =
      deriv (fun ν => scalarStateResidual D S
        (n07aNuParameterState hT hS h01.1.2.2.2.1 (((A z).1.1, ν), (A z).2)) p)
          (A z).1.2 := data.choose_spec.2.2.choose_spec.2 (A z) (hmaps hz) p
  exact hdecode.trans (n07aNuSource_reducedDerivative_eq hS hT h01
    (A z) (liftSectorParameter S C z) hcoord p)

end ContinuousFlexibility.Analysis
