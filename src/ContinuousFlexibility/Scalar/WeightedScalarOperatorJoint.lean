module

public import ContinuousFlexibility.Scalar.WeightedScalarOperatorGerms
public import ContinuousFlexibility.Scalar.WeightedScalarOperatorSmooth
public import ContinuousFlexibility.Scalar.WeightedHeightParameterPullback

/-!
# Joint scalar operator families on the required product domains

The state domain may be restricted, while the common height and independent
source height range over their full spaces. The same actual maps also
have uniform germs at zero in those homogeneous arguments.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X} {U : Set X}
  {a b c t : X → ScalarHeightSpace S}

theorem scalarCoefficientOperatorCLM_jointUniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (ha : UniformTameGerm p (scalarHeightGrading S) x0 a)
    (hb : UniformTameGerm p (scalarHeightGrading S) x0 b)
    (hc : UniformTameGerm p (scalarHeightGrading S) x0 c) :
    UniformTameGerm (pairGrading p (scalarCommonHeightGrading S))
      (scalarHeightGrading S) (x0, (0 : ScalarCommonHeight S))
      (fun z : X × ScalarCommonHeight S =>
        scalarCoefficientOperatorCLM hD hT hS (a z.1) (b z.1) (c z.1) z.2) := by
  have hpc := weighted_scalarCommonHeightGrading_monotone S
  have htc := weighted_scalarCommonHeightGrading_withSeminorms S
  have ha' := scalarHeight_uniformTameGerm_fst hS hp ht hpc htc
    (0 : ScalarCommonHeight S) ha
  have hb' := scalarHeight_uniformTameGerm_fst hS hp ht hpc htc
    (0 : ScalarCommonHeight S) hb
  have hc' := scalarHeight_uniformTameGerm_fst hS hp ht hpc htc
    (0 : ScalarCommonHeight S) hc
  have hu := uniformTameGerm_continuousLinear (withSeminorms_pairGrading ht htc)
    (x0, (0 : ScalarCommonHeight S))
    (ContinuousLinearMap.snd ℝ X (ScalarCommonHeight S))
    (scalar_pair_snd_isTame p (scalarCommonHeightGrading S))
  exact scalarCoefficientOperatorCLM_uniformTameGerm hD hT hS
    (tamePairGrading_monotone hp hpc) (withSeminorms_pairGrading ht htc) ha' hb' hc' hu

theorem scalarTypeErrorLinear_jointUniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (htype : UniformTameGerm p (scalarHeightGrading S) x0 t) :
    UniformTameGerm (pairGrading (pairGrading p (scalarHeightGrading S))
        (scalarCommonHeightGrading S)) (scalarHeightGrading S)
      ((x0, (0 : ScalarHeightSpace S)), (0 : ScalarCommonHeight S))
      (fun z : (X × ScalarHeightSpace S) × ScalarCommonHeight S =>
        scalarTypeErrorLinear hD hT hS (t z.1.1) z.1.2 z.2) := by
  have hph := weighted_scalarHeightGrading_monotone S
  have hth := weighted_scalarHeightGrading_withSeminorms S
  have hpc := weighted_scalarCommonHeightGrading_monotone S
  have htc := weighted_scalarCommonHeightGrading_withSeminorms S
  have hp1 := tamePairGrading_monotone hp hph
  have ht1 := withSeminorms_pairGrading ht hth
  have ht0 := scalarHeight_uniformTameGerm_fst hS hp ht hph hth
    (0 : ScalarHeightSpace S) htype
  have hR0 : UniformTameGerm (pairGrading p (scalarHeightGrading S))
      (scalarHeightGrading S) (x0, (0 : ScalarHeightSpace S))
      (fun z : X × ScalarHeightSpace S => z.2) :=
    uniformTameGerm_continuousLinear ht1 (x0, (0 : ScalarHeightSpace S))
      (ContinuousLinearMap.snd ℝ X (ScalarHeightSpace S))
      (scalar_pair_snd_isTame p (scalarHeightGrading S))
  have ht' := scalarHeight_uniformTameGerm_fst hS hp1 ht1 hpc htc
    (0 : ScalarCommonHeight S) ht0
  have hR := scalarHeight_uniformTameGerm_fst hS hp1 ht1 hpc htc
    (0 : ScalarCommonHeight S) hR0
  have hu := uniformTameGerm_continuousLinear (withSeminorms_pairGrading ht1 htc)
    ((x0, (0 : ScalarHeightSpace S)), (0 : ScalarCommonHeight S))
    (ContinuousLinearMap.snd ℝ (X × ScalarHeightSpace S) (ScalarCommonHeight S))
    (scalar_pair_snd_isTame (pairGrading p (scalarHeightGrading S))
      (scalarCommonHeightGrading S))
  exact scalarTypeErrorLinear_uniformTameGerm hD hT hS
    (tamePairGrading_monotone hp1 hpc) (withSeminorms_pairGrading ht1 htc) ht' hR hu

theorem scalarCoefficientOperatorCLM_jointSmoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) (hU : IsOpen U)
    (ha : SmoothTameOn p (scalarHeightGrading S) U a)
    (hb : SmoothTameOn p (scalarHeightGrading S) U b)
    (hc : SmoothTameOn p (scalarHeightGrading S) U c) :
    SmoothTameOn (pairGrading p (scalarCommonHeightGrading S))
      (scalarHeightGrading S) (U ×ˢ univ)
      (fun z : X × ScalarCommonHeight S =>
        scalarCoefficientOperatorCLM hD hT hS (a z.1) (b z.1) (c z.1) z.2) := by
  have hpc := weighted_scalarCommonHeightGrading_monotone S
  have htc := weighted_scalarCommonHeightGrading_withSeminorms S
  have ha' := scalarHeight_smoothTameOn_fst hS hp ht hpc htc hU ha
  have hb' := scalarHeight_smoothTameOn_fst hS hp ht hpc htc hU hb
  have hc' := scalarHeight_smoothTameOn_fst hS hp ht hpc htc hU hc
  have hu := smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
    (ContinuousLinearMap.snd ℝ X (ScalarCommonHeight S))
    (scalar_pair_snd_isTame p (scalarCommonHeightGrading S))
  exact scalarCoefficientOperatorCLM_smoothTameOn hD hT hS
    (tamePairGrading_monotone hp hpc) (withSeminorms_pairGrading ht htc) ha' hb' hc' hu

theorem scalarTypeErrorLinear_jointSmoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) (hU : IsOpen U)
    (htype : SmoothTameOn p (scalarHeightGrading S) U t) :
    SmoothTameOn (pairGrading (pairGrading p (scalarHeightGrading S))
        (scalarCommonHeightGrading S)) (scalarHeightGrading S) ((U ×ˢ univ) ×ˢ univ)
      (fun z : (X × ScalarHeightSpace S) × ScalarCommonHeight S =>
        scalarTypeErrorLinear hD hT hS (t z.1.1) z.1.2 z.2) := by
  have hph := weighted_scalarHeightGrading_monotone S
  have hth := weighted_scalarHeightGrading_withSeminorms S
  have hpc := weighted_scalarCommonHeightGrading_monotone S
  have htc := weighted_scalarCommonHeightGrading_withSeminorms S
  have hp1 := tamePairGrading_monotone hp hph
  have ht1 := withSeminorms_pairGrading ht hth
  have ht0 := scalarHeight_smoothTameOn_fst hS hp ht hph hth hU htype
  have hR0 : SmoothTameOn (pairGrading p (scalarHeightGrading S))
      (scalarHeightGrading S) (U ×ˢ univ) (fun z : X × ScalarHeightSpace S => z.2) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.snd ℝ X (ScalarHeightSpace S))
      (scalar_pair_snd_isTame p (scalarHeightGrading S))
  have ht' := scalarHeight_smoothTameOn_fst hS hp1 ht1 hpc htc
    (hU.prod isOpen_univ) ht0
  have hR := scalarHeight_smoothTameOn_fst hS hp1 ht1 hpc htc
    (hU.prod isOpen_univ) hR0
  have hu := smoothTameOn_continuousLinear_on ((hU.prod isOpen_univ).prod isOpen_univ)
    (ContinuousLinearMap.snd ℝ (X × ScalarHeightSpace S) (ScalarCommonHeight S))
    (scalar_pair_snd_isTame (pairGrading p (scalarHeightGrading S))
      (scalarCommonHeightGrading S))
  exact scalarTypeErrorLinear_smoothTameOn hD hT hS
    (tamePairGrading_monotone hp1 hpc) (withSeminorms_pairGrading ht1 htc) ht' hR hu

end ContinuousFlexibility.Statements
