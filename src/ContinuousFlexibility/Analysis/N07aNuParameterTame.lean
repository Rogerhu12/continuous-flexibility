import ContinuousFlexibility.Analysis.N07aNuProfileTame
import ContinuousFlexibility.Scalar.WeightedHeightParameterPullback
import ContinuousFlexibility.Scalar.WeightedCommonHeightCalculus

/-!
# The border-only scalar state has a genuine tame parameterization

The reduced parameter retains the common height, the border scalar and q.
No optical control is needed for the distinguished column. The map into
the existing weighted scalar state is assembled from the actual compact
profile germ and fixed coordinate projections.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

abbrev N07aNuParameter (S : PhysicalSpacesData) := (ScalarCommonHeight S × ℝ) × ℝ

def n07aNuParameterGrading (S : PhysicalSpacesData) : ℕ → Seminorm ℝ (N07aNuParameter S) :=
  pairGrading (pairGrading (scalarCommonHeightGrading S) realGrading) realGrading

def n07aNuParameterCenter (S : PhysicalSpacesData) (v₀ : ScalarHeightSpace S) :
    N07aNuParameter S := (((v₀, 0), 0), 0)

theorem n07aNuParameterGrading_monotone (S : PhysicalSpacesData) :
    Monotone (n07aNuParameterGrading S) :=
  tamePairGrading_monotone
    (tamePairGrading_monotone (weighted_scalarCommonHeightGrading_monotone S)
      weighted_realGrading_monotone) weighted_realGrading_monotone

theorem n07aNuParameterGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (n07aNuParameterGrading S) :=
  withSeminorms_pairGrading
    (withSeminorms_pairGrading (weighted_scalarCommonHeightGrading_withSeminorms S)
      weighted_realGrading_withSeminorms) weighted_realGrading_withSeminorms

def n07aNuCommonCLM (S : PhysicalSpacesData) : N07aNuParameter S →L[ℝ] ScalarCommonHeight S :=
  (ContinuousLinearMap.fst ℝ (ScalarCommonHeight S) ℝ).comp
    (ContinuousLinearMap.fst ℝ (ScalarCommonHeight S × ℝ) ℝ)

def n07aNuScalarCLM (S : PhysicalSpacesData) : N07aNuParameter S →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (ScalarCommonHeight S) ℝ).comp
    (ContinuousLinearMap.fst ℝ (ScalarCommonHeight S × ℝ) ℝ)

theorem n07aNuCommonCLM_apply (S : PhysicalSpacesData) (x : N07aNuParameter S) :
    n07aNuCommonCLM S x = x.1.1 := by
  simp only [n07aNuCommonCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']

theorem n07aNuScalarCLM_apply (S : PhysicalSpacesData) (x : N07aNuParameter S) :
    n07aNuScalarCLM S x = x.1.2 := by
  simp only [n07aNuScalarCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

theorem n07aNuCommonCLM_isTame (S : PhysicalSpacesData) :
    IsTameLinear (n07aNuParameterGrading S) (scalarCommonHeightGrading S)
      (n07aNuCommonCLM S).toLinearMap 0 0 :=
  (scalar_pair_fst_isTame (scalarCommonHeightGrading S) realGrading).comp
    (scalar_pair_fst_isTame (pairGrading (scalarCommonHeightGrading S) realGrading) realGrading)

theorem n07aNuScalarCLM_isTame (S : PhysicalSpacesData) :
    IsTameLinear (n07aNuParameterGrading S) realGrading
      (n07aNuScalarCLM S).toLinearMap 0 0 :=
  (scalar_pair_snd_isTame (scalarCommonHeightGrading S) realGrading).comp
    (scalar_pair_fst_isTame (pairGrading (scalarCommonHeightGrading S) realGrading) realGrading)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n07aNuParameterState
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hb : RadialTrueBorder D) (x : N07aNuParameter S) : ScalarWeightedState S :=
  (((n07aNuProfileHeight hT hS hb scalarBeta x.1.2, x.1.1.1), x.1.1.2), x.2)

theorem n07aNuParameterState_center
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hb : RadialTrueBorder D) (v₀ : ScalarHeightSpace S) :
    n07aNuParameterState hT hS hb (n07aNuParameterCenter S v₀) = scalarStateCenter S v₀ := by
  simp only [n07aNuParameterState, n07aNuParameterCenter,
    n07aNuProfileHeight_zero, scalarStateCenter]

theorem n07aNuParameterState_uniformTameGerm
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hb : RadialTrueBorder D) (v₀ : ScalarHeightSpace S) :
    UniformTameGerm (n07aNuParameterGrading S) (scalarStateGrading S)
      (n07aNuParameterCenter S v₀) (n07aNuParameterState hT hS hb) := by
  let : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  let : ContinuousSMul ℝ (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).continuousSMul
  let : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  have hp := n07aNuParameterGrading_monotone S
  have ht := n07aNuParameterGrading_withSeminorms S
  have hn := uniformTameGerm_continuousLinear ht (n07aNuParameterCenter S v₀)
    (n07aNuScalarCLM S) (n07aNuScalarCLM_isTame S)
  have hm := hn.comp (n07aNuProfileHeight_uniformTameGerm hT hS hb scalarBeta_pos)
    hp ht weighted_realGrading_monotone
  have hv := uniformTameGerm_continuousLinear ht (n07aNuParameterCenter S v₀)
    ((scalarCommonProjectionCLM S).comp (n07aNuCommonCLM S))
    ((scalarCommonProjectionCLM_isTame S).comp (n07aNuCommonCLM_isTame S))
  have hl := uniformTameGerm_continuousLinear ht (n07aNuParameterCenter S v₀)
    ((ContinuousLinearMap.snd ℝ (ScalarHeightSpace S) ℝ).comp (n07aNuCommonCLM S))
    ((scalar_pair_snd_isTame (scalarHeightGrading S) realGrading).comp
      (n07aNuCommonCLM_isTame S))
  have hq := uniformTameGerm_continuousLinear ht (n07aNuParameterCenter S v₀)
    (ContinuousLinearMap.snd ℝ (ScalarCommonHeight S × ℝ) ℝ)
    (scalar_pair_snd_isTame (pairGrading (scalarCommonHeightGrading S) realGrading) realGrading)
  have hstate := ((hm.prodMk hv hp ht).prodMk hl hp ht).prodMk hq hp ht
  apply hstate.congr
  intro x
  simp only [Function.comp_apply, n07aNuScalarCLM_apply, n07aNuCommonCLM_apply,
    ContinuousLinearMap.comp_apply, scalarCommonProjectionCLM,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', n07aNuParameterState]

end ContinuousFlexibility.Analysis
