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
  rw [n07aNuSectorProjectionCLM, ContinuousLinearMap.comp_apply,
    n07aSectorParameterInclusion_apply, n07aNuRawProjectionCLM_apply]

theorem n07aNuSectorProjectionCLM_grading_le (S : PhysicalSpacesData) (n : ℕ)
    (z : StateDirections S × ℝ) :
    n07aNuParameterGrading S n (n07aNuSectorProjectionCLM S z) ≤
      n07aParameterGrading S n z := by
  simp only [n07aNuSectorProjectionCLM_apply, n07aNuParameterGrading,
    n07aParameterGrading, scalarCommonHeightGrading, scalarHeightGrading,
    sectorGrading, stateGrading, heightPairGrading, pairGrading_apply,
    Seminorm.comp_apply, Submodule.subtype_apply, realGrading, coe_normSeminorm]
  have hκ := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) z.1.val.2.2.1
  have hα := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) z.1.val.2.2.2
  linarith only [hκ, hα]

theorem n07aNuSectorProjectionCLM_center
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (z : StateDirections S × ℝ) :
    n07aNuParameterCenter S C.referenceState.1.1 + n07aNuSectorProjectionCLM S z =
      n07aNuRawProjectionCLM S (liftSectorParameter S C z) := by
  simp only [n07aNuParameterCenter, n07aNuSectorProjectionCLM_apply,
    n07aNuRawProjectionCLM_apply, liftSectorParameter, Prod.fst_add, Prod.snd_add,
    Prod.mk_add_mk, href.2.1, href.2.2.1, zero_add]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

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
  letI : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  let data := n07a_exists_nuReducedSource h01.1.1 hT hS h01.1.2.2.2.1
    C.referenceState.1.1
  let U : Set (N07aNuParameter S) := data.choose
  have hU : IsOpen U := data.choose_spec.1
  have hcenter : n07aNuParameterCenter S C.referenceState.1.1 ∈ U := data.choose_spec.2.1
  let N : N07aNuParameter S → S.Source := data.choose_spec.2.2.choose
  have hN : SmoothTameOn (n07aNuParameterGrading S) S.sourceGrading U N :=
    data.choose_spec.2.2.choose_spec.1
  have hdecode := data.choose_spec.2.2.choose_spec.2
  let c := n07aNuParameterCenter S C.referenceState.1.1
  let L := n07aNuSectorProjectionCLM S
  let A : (StateDirections S × ℝ) → N07aNuParameter S := fun z => c + L z
  have hA : Continuous A := continuous_const.add L.continuous
  have hA0 : A 0 ∈ U := by simpa only [A, map_zero, add_zero] using hcenter
  have hAU : A ⁻¹' U ∈ 𝓝 (0 : StateDirections S × ℝ) :=
    (hU.preimage hA).mem_nhds hA0
  obtain ⟨base', η, hbase, hη, _, hsub⟩ := exists_small_uniformTameBall
    (n07aParameterGrading_monotone S) (n07aParameterGrading_withSeminorms S) hAU base
  let ε' : ℝ := min ε (η / 2)
  have he : 0 < ε' := lt_min h01.2.1 (half_pos hη)
  have hmaps : sectorNeighborhood S base' ε' ε' ⊆ A ⁻¹' U := by
    intro z hz
    apply hsub
    change n07aParameterGrading S base' (z - 0) < η
    simp only [sub_zero, n07aParameterGrading, pairGrading_apply,
      realGrading, coe_normSeminorm, Real.norm_eq_abs]
    have hη' : ε' ≤ η / 2 := min_le_right _ _
    linarith only [hz.1, hz.2, hη']
  have hpull := n07a_smoothTameOn_affine_nonexpansive hN c L
    (n07aNuSectorProjectionCLM_grading_le S)
  refine ⟨base', hbase, ε', he, min_le_left _ _, N ∘ A,
    smoothTameOn_mono hpull (n07a_sectorNeighborhood_isOpen S base' ε' ε') hmaps, ?_⟩
  intro z hz p
  have hcoord : A z = n07aNuRawProjectionCLM S (liftSectorParameter S C z) :=
    n07aNuSectorProjectionCLM_center h01.2.2.1 z
  rw [Function.comp_apply, hdecode (A z) (hmaps hz) p,
    n07a_nuColumnField_eq_pureResidual_deriv hS hT h01, hcoord,
    n07aNuRawProjectionCLM_apply] <;> rfl

end ContinuousFlexibility.Analysis
