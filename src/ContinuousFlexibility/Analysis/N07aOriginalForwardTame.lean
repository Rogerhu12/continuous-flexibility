module

public import ContinuousFlexibility.Analysis.N07aOriginalForward
public import ContinuousFlexibility.Analysis.N07aMixedCoefficientTame
public import ContinuousFlexibility.Analysis.SolveTameSubspace
public import ContinuousFlexibility.Scalar.WeightedScalarOperatorJoint

/-!
# The actual original forward family is smooth tame into Source

The coefficient families are the N01 fields already lifted into their
physical height models. The target restriction uses the proved physical
conservation identity, so its source decoder is unchanged.
-/

@[expose] public section

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n07aOriginalForwardHeightCLM_smoothTame
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) :
    SmoothTameOn (pairGrading (n07aParameterGrading S) (scalarCommonHeightGrading S))
      (S.height scalarBeta).grading
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ScalarCommonHeight S =>
        n07aOriginalForwardHeightCLM hS hT h01 z.1 z.2) := by
  have hp := n07aParameterGrading_monotone S
  have ht := n07aParameterGrading_withSeminorms S
  have hU := n07a_sectorNeighborhood_isOpen S base ε ε
  have hzero : SmoothTameOn (n07aParameterGrading S) (scalarHeightGrading S)
      (sectorNeighborhood S base ε ε) (fun _ => (0 : ScalarHeightSpace S)) :=
    (fixedNeighborhoodSmoothTame_const (base := 0) (loss := 0) 0 hU).1
  have hreference := scalarCoefficientOperatorCLM_jointSmoothTameOn h01.1.1 hT hS
    hp ht hU hzero hzero hzero
  have ha := n07aDiagonalCoefficientHeight_smoothTame hS hT h01
    (by norm_num : (1 / 64 : ℝ) < 3 / 64) 0 (by decide)
  have hb := n07aMixedCoefficientHeight_smoothTame hS hT h01
    (by norm_num : (1 / 64 : ℝ) < 3 / 64)
  have hc := n07aDiagonalCoefficientHeight_smoothTame hS hT h01
    (by norm_num : (1 / 64 : ℝ) < 3 / 64) 2 (by decide)
  have hperturbation := n07aMixedCoefficientOperator_jointSmoothTame h01.1.1 hT hS
    (by norm_num : (0 : ℝ) ≤ 1 / 64) hp ht hU ha hb hc
  apply smoothTameOn_congr (smoothTameOn_add
    (tamePairGrading_monotone hp (weighted_scalarCommonHeightGrading_monotone S))
    hreference hperturbation)
  intro z _
  exact (n07aOriginalForwardHeightCLM_apply hS hT h01 z.1 z.2).symm

theorem n07aOriginalForwardCLM_smoothTame
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) :
    SmoothTameOn (n07aParameterHeightGrading S) S.sourceGrading
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S =>
        n07aOriginalForwardCLM hS hT h01 z.1 z.2) := by
  let : IsTopologicalAddGroup (StateDirections S × ℝ) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  let : ContinuousSMul ℝ (StateDirections S × ℝ) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  exact solve_smoothTameOn_codRestrict S.Q.toLinearMap.ker S.Q.isClosed_ker
    (n07aOriginalForwardHeightCLM_smoothTame hS hT h01)
    (fun z : (StateDirections S × ℝ) × HeightPair S =>
      n07aOriginalForwardCLM hS hT h01 z.1 z.2)
    (fun z _ => n07aOriginalForwardCLM_apply_val hS hT h01 z.1 z.2)

end ContinuousFlexibility.Analysis
