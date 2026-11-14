module

public import ContinuousFlexibility.Scalar.WeightedCandidateOperators
public import ContinuousFlexibility.Scalar.WeightedScalarCandidateGerms
public import ContinuousFlexibility.Scalar.WeightedScalarOperatorJoint

/-!
# Actual candidate operator families and their common smooth domain

The concrete coefficient formulas supply all analytic assumptions used by
the joint operator calculus. One intersection of four state neighborhoods
works for both full operator parameter domains.
-/

@[expose] public section

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

/-- Extract a common domain while the four coefficient functions remain abstract. -/
private theorem exists_scalarOperators_jointSmoothTameOn_of_germs
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S)
    (a b c t : ScalarWeightedState S → ScalarHeightSpace S)
    (hga : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 a)
    (hgb : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 b)
    (hgc : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 c)
    (hgt : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 t) :
    ∃ V : Set (ScalarWeightedState S), IsOpen V ∧ x0 ∈ V ∧
      SmoothTameOn (pairGrading (scalarStateGrading S) (scalarCommonHeightGrading S))
        (scalarHeightGrading S) (V ×ˢ univ)
        (fun z : ScalarWeightedState S × ScalarCommonHeight S =>
          scalarCoefficientOperatorCLM hD hT hS (a z.1) (b z.1) (c z.1) z.2) ∧
      SmoothTameOn
        (pairGrading (pairGrading (scalarStateGrading S) (scalarHeightGrading S))
          (scalarCommonHeightGrading S)) (scalarHeightGrading S) ((V ×ˢ univ) ×ˢ univ)
        (fun z : (ScalarWeightedState S × ScalarHeightSpace S) × ScalarCommonHeight S =>
          scalarTypeErrorLinear hD hT hS (t z.1.1) z.1.2 z.2) := by
  obtain ⟨ba, la, ea, hea, hfa⟩ := hga
  obtain ⟨bb, lb, eb, heb, hfb⟩ := hgb
  obtain ⟨bc, lc, ec, hec, hfc⟩ := hgc
  obtain ⟨bt, lt, et, het, hft⟩ := hgt
  let Ua : Set (ScalarWeightedState S) :=
    {x | scalarStateGrading S ba (x - x0) < ea}
  let Ub : Set (ScalarWeightedState S) :=
    {x | scalarStateGrading S bb (x - x0) < eb}
  let Uc : Set (ScalarWeightedState S) :=
    {x | scalarStateGrading S bc (x - x0) < ec}
  let Ut : Set (ScalarWeightedState S) :=
    {x | scalarStateGrading S bt (x - x0) < et}
  let V := (Ua ∩ Ub) ∩ (Uc ∩ Ut)
  have hp := weighted_scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hUa : IsOpen Ua := isOpen_uniformTameBall ht ba x0 ea
  have hUb : IsOpen Ub := isOpen_uniformTameBall ht bb x0 eb
  have hUc : IsOpen Uc := isOpen_uniformTameBall ht bc x0 ec
  have hUt : IsOpen Ut := isOpen_uniformTameBall ht bt x0 et
  have hV : IsOpen V := (hUa.inter hUb).inter (hUc.inter hUt)
  have hzero (s : ℕ) : scalarStateGrading S s (0 : ScalarWeightedState S) = 0 :=
    (scalarStateGrading S s).map_zero'
  have hxa : x0 ∈ Ua := by
    simpa only [Ua, Set.mem_setOf_eq, sub_self, hzero ba] using hea
  have hxb : x0 ∈ Ub := by
    simpa only [Ub, Set.mem_setOf_eq, sub_self, hzero bb] using heb
  have hxc : x0 ∈ Uc := by
    simpa only [Uc, Set.mem_setOf_eq, sub_self, hzero bc] using hec
  have hxt : x0 ∈ Ut := by
    simpa only [Ut, Set.mem_setOf_eq, sub_self, hzero bt] using het
  have ha : SmoothTameOn (scalarStateGrading S) (scalarHeightGrading S) V
      a :=
    (hfa.restrict hV (fun _ hx => hx.1.1)).1
  have hb : SmoothTameOn (scalarStateGrading S) (scalarHeightGrading S) V
      b :=
    (hfb.restrict hV (fun _ hx => hx.1.2)).1
  have hc : SmoothTameOn (scalarStateGrading S) (scalarHeightGrading S) V
      c :=
    (hfc.restrict hV (fun _ hx => hx.2.1)).1
  have htype : SmoothTameOn (scalarStateGrading S) (scalarHeightGrading S) V
      t :=
    (hft.restrict hV (fun _ hx => hx.2.2)).1
  refine ⟨V, hV, ⟨⟨hxa, hxb⟩, ⟨hxc, hxt⟩⟩, ?_, ?_⟩
  · exact scalarCoefficientOperatorCLM_jointSmoothTameOn hD hT hS hp ht hV ha hb hc
  · exact scalarTypeErrorLinear_jointSmoothTameOn hD hT hS hp ht hV htype

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
  exact exists_scalarOperators_jointSmoothTameOn_of_germs hD hT hS
    (scalarStateCenter S v0)
    (scalarCoefficientAHeight hD hT hS) (scalarCoefficientBPrimitive hD hT hS)
    (scalarCoefficientCHeight hD hT hS) (scalarTypePerturbationHeight hD hT hS)
    (scalarCoefficientAHeight_uniformTameGerm hD hT hS v0)
    (scalarCoefficientBPrimitive_uniformTameGerm hD hT hS v0)
    (scalarCoefficientCHeight_uniformTameGerm hD hT hS v0)
    (scalarTypePerturbationHeight_uniformTameGerm hD hT hS v0)

end ContinuousFlexibility.Statements
