import ContinuousFlexibility.Scalar.WeightedCandidateOperators
import ContinuousFlexibility.Scalar.WeightedScalarCandidateGerms
import ContinuousFlexibility.Scalar.WeightedScalarOperatorJoint

/-!
# Actual candidate operator families and their common smooth domain

The concrete coefficient formulas supply all analytic assumptions used by
the joint operator calculus. One intersection of four state neighborhoods
works for both full operator parameter domains.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem scalarCandidateLinear_jointUniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm
      (pairGrading (scalarStateGrading S) (scalarCommonHeightGrading S))
      (scalarHeightGrading S) (scalarStateCenter S v0, (0 : ScalarCommonHeight S))
      (fun z : ScalarWeightedState S × ScalarCommonHeight S =>
        scalarCandidateLinear hD hT hS z.1 z.2) := by
  exact scalarCoefficientOperatorCLM_jointUniformTameGerm hD hT hS
    (weighted_scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)
    (scalarCoefficientAHeight_uniformTameGerm hD hT hS v0)
    (scalarCoefficientBPrimitive_uniformTameGerm hD hT hS v0)
    (scalarCoefficientCHeight_uniformTameGerm hD hT hS v0)

theorem scalarCandidateError_jointUniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm
      (pairGrading (pairGrading (scalarStateGrading S) (scalarHeightGrading S))
        (scalarCommonHeightGrading S)) (scalarHeightGrading S)
      ((scalarStateCenter S v0, (0 : ScalarHeightSpace S)), (0 : ScalarCommonHeight S))
      (fun z : (ScalarWeightedState S × ScalarHeightSpace S) × ScalarCommonHeight S =>
        scalarCandidateError hD hT hS z.1.1 z.1.2 z.2) := by
  exact scalarTypeErrorLinear_jointUniformTameGerm hD hT hS
    (weighted_scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)
    (scalarTypePerturbationHeight_uniformTameGerm hD hT hS v0)

/-- One actual open state neighborhood supports both full joint smooth
tame families, with no restrictions on their independent height arguments. -/
theorem exists_scalarCandidateOperators_jointSmoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    ∃ V : Set (ScalarWeightedState S), IsOpen V ∧ scalarStateCenter S v0 ∈ V ∧
      SmoothTameOn (pairGrading (scalarStateGrading S) (scalarCommonHeightGrading S))
        (scalarHeightGrading S) (V ×ˢ univ)
        (fun z : ScalarWeightedState S × ScalarCommonHeight S =>
          scalarCandidateLinear hD hT hS z.1 z.2) ∧
      SmoothTameOn
        (pairGrading (pairGrading (scalarStateGrading S) (scalarHeightGrading S))
          (scalarCommonHeightGrading S)) (scalarHeightGrading S) ((V ×ˢ univ) ×ˢ univ)
        (fun z : (ScalarWeightedState S × ScalarHeightSpace S) × ScalarCommonHeight S =>
          scalarCandidateError hD hT hS z.1.1 z.1.2 z.2) := by
  obtain ⟨ba, la, ea, hea, hfa⟩ := scalarCoefficientAHeight_uniformTameGerm hD hT hS v0
  obtain ⟨bb, lb, eb, heb, hfb⟩ := scalarCoefficientBPrimitive_uniformTameGerm hD hT hS v0
  obtain ⟨bc, lc, ec, hec, hfc⟩ := scalarCoefficientCHeight_uniformTameGerm hD hT hS v0
  obtain ⟨bt, lt, et, het, hft⟩ := scalarTypePerturbationHeight_uniformTameGerm hD hT hS v0
  let Ua : Set (ScalarWeightedState S) :=
    {x | scalarStateGrading S ba (x - scalarStateCenter S v0) < ea}
  let Ub : Set (ScalarWeightedState S) :=
    {x | scalarStateGrading S bb (x - scalarStateCenter S v0) < eb}
  let Uc : Set (ScalarWeightedState S) :=
    {x | scalarStateGrading S bc (x - scalarStateCenter S v0) < ec}
  let Ut : Set (ScalarWeightedState S) :=
    {x | scalarStateGrading S bt (x - scalarStateCenter S v0) < et}
  let V := (Ua ∩ Ub) ∩ (Uc ∩ Ut)
  have hp := weighted_scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hUa : IsOpen Ua := isOpen_uniformTameBall ht ba (scalarStateCenter S v0) ea
  have hUb : IsOpen Ub := isOpen_uniformTameBall ht bb (scalarStateCenter S v0) eb
  have hUc : IsOpen Uc := isOpen_uniformTameBall ht bc (scalarStateCenter S v0) ec
  have hUt : IsOpen Ut := isOpen_uniformTameBall ht bt (scalarStateCenter S v0) et
  have hV : IsOpen V := (hUa.inter hUb).inter (hUc.inter hUt)
  have hzero (s : ℕ) : scalarStateGrading S s (0 : ScalarWeightedState S) = 0 :=
    (scalarStateGrading S s).map_zero'
  have hxa : scalarStateCenter S v0 ∈ Ua := by
    simpa only [Ua, Set.mem_setOf_eq, sub_self, hzero ba] using hea
  have hxb : scalarStateCenter S v0 ∈ Ub := by
    simpa only [Ub, Set.mem_setOf_eq, sub_self, hzero bb] using heb
  have hxc : scalarStateCenter S v0 ∈ Uc := by
    simpa only [Uc, Set.mem_setOf_eq, sub_self, hzero bc] using hec
  have hxt : scalarStateCenter S v0 ∈ Ut := by
    simpa only [Ut, Set.mem_setOf_eq, sub_self, hzero bt] using het
  have ha : SmoothTameOn (scalarStateGrading S) (scalarHeightGrading S) V
      (scalarCoefficientAHeight hD hT hS) :=
    (hfa.restrict hV (fun _ hx => hx.1.1)).1
  have hb : SmoothTameOn (scalarStateGrading S) (scalarHeightGrading S) V
      (scalarCoefficientBPrimitive hD hT hS) :=
    (hfb.restrict hV (fun _ hx => hx.1.2)).1
  have hc : SmoothTameOn (scalarStateGrading S) (scalarHeightGrading S) V
      (scalarCoefficientCHeight hD hT hS) :=
    (hfc.restrict hV (fun _ hx => hx.2.1)).1
  have htype : SmoothTameOn (scalarStateGrading S) (scalarHeightGrading S) V
      (scalarTypePerturbationHeight hD hT hS) :=
    (hft.restrict hV (fun _ hx => hx.2.2)).1
  refine ⟨V, hV, ⟨⟨hxa, hxb⟩, ⟨hxc, hxt⟩⟩, ?_, ?_⟩
  · exact scalarCoefficientOperatorCLM_jointSmoothTameOn hD hT hS hp ht hV ha hb hc
  · exact scalarTypeErrorLinear_jointSmoothTameOn hD hT hS hp ht hV htype

end ContinuousFlexibility.Statements
