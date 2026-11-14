module

public import ContinuousFlexibility.Scalar.WeightedScalarCandidates
public import ContinuousFlexibility.Scalar.WeightedStateBasicGerms
public import ContinuousFlexibility.Scalar.WeightedUniformTameGermFinite

/-!
# Genuine uniform tame germs of every concrete scalar candidate

The finite formulas use the actual weighted products, actual spatial
derivatives, and canonical scalar compositions.  Their fixed bases and losses
are selected before all directional orders.  Finite pairing and the prescribed
sum grading assemble the seven jets and three coefficient fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

section Actions

variable {x0 : ScalarWeightedState S} {f : ScalarWeightedState S → ScalarHeightSpace S}

theorem UniformTameGerm.scalarStateSlopeAct
    (hf : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (fun x => scalarStateSlopeAct hD hT hS x (f x)) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact (hf.scalarStateWAct hD hT hS).add
    ((scalarStateRadialHeight_uniformTameGerm hD hT hS x0).scalarHeightMul hf hT hS hp ht) hp ht

theorem UniformTameGerm.scalarStateSlopeOddAct
    (hf : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (fun x => scalarStateSlopeOddAct hD hT hS x (f x)) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact (hf.scalarStateWOddAct hD hT hS).add
    ((scalarStateRadialHeight_uniformTameGerm hD hT hS x0).scalarHeightOddMul hf hT hS hp ht) hp ht

theorem UniformTameGerm.scalarStateWDerivAct
    (hf : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (fun x => scalarStateWDerivAct hD hT hS x (f x)) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hm := scalarStateMeanCLM_uniformTameGerm hD hT hS x0
  have hmd := scalarStateMeanDerivCLM_uniformTameGerm hD hT hS x0
  exact ((hm.scalarHeightUnitalAct hf hT hS hp ht).scalarReferenceWDeriv hD hT hS hp ht).add
    ((hmd.scalarHeightMul hf hT hS hp ht).scalarReferenceW hD hT hS hp ht) hp ht

end Actions

theorem scalarStateDPower_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) (α : ℝ) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarStateDPower hD hT hS α) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact (scalarStateDiscriminantHeight_uniformTameGerm hD hT hS
    (scalarStateCenter S v0)).scalarHeightPower
      (scalarStateDiscriminantHeight_center hD hT hS v0) hT hS α hp ht

theorem scalarStateAngularPower_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) (α : ℝ) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarStateAngularPower hD hT hS α) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have ha := scalarStateAngularSquare_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hz : -scalarStateAngularSquare hD hT hS (scalarStateCenter S v0) = 0 := by
    rw [scalarStateAngularSquare_center, neg_zero]
  exact (ha.neg hp ht).scalarHeightPower hz hT hS α hp ht

theorem scalarStateQPower_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) (α : ℝ) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarStateQPower hD hT hS α) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact (scalarStateQuotientHeight_uniformTameGerm hD hT hS v0).scalarHeightPower
    (scalarStateQuotientHeight_center hD hT hS v0) hT hS α hp ht

theorem scalarStateConnectionFactor_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarStateConnectionFactor hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact (scalarStateAngularPower_uniformTameGerm hD hT hS v0 (-1)).scalarHeightUnitalMul
    (scalarStateDPower_uniformTameGerm hD hT hS v0 (-(1 / 2))) hT hS hp ht

theorem scalarJetCoframeRadialHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarJetCoframeRadialHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact (scalarStateDPower_uniformTameGerm hD hT hS v0 (1 / 2)).scalarHeightUnitalMul
    (scalarStateAngularPower_uniformTameGerm hD hT hS v0 (-(1 / 2))) hT hS hp ht

theorem scalarJetCoframeMixedPrimitive_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarJetCoframeMixedPrimitive hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have ha := (scalarStateAngularPrimitive_uniformTameGerm hD hT hS
    (scalarStateCenter S v0)).scalarStateSlopeOddAct hD hT hS
  exact ((scalarStateAngularPower_uniformTameGerm hD hT hS v0 (-(1 / 2))).scalarHeightOddUnitalAct
    ha hT hS hp ht).neg hp ht

theorem scalarJetCoframeAngularHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarJetCoframeAngularHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact (scalarStateAngularPower_uniformTameGerm hD hT hS v0 (1 / 2)).scalarReferenceRadius
    hD hT hS hp ht

theorem scalarJetConnectionRadialPrimitive_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarJetConnectionRadialPrimitive hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hc := scalarStateConnectionFactor_uniformTameGerm hD hT hS v0
  have hm := (scalarStateMixedPrimitive_uniformTameGerm hD hT hS
    (scalarStateCenter S v0)).scalarStateSlopeOddAct hD hT hS
  exact hc.scalarHeightOddUnitalAct hm hT hS hp ht

theorem scalarJetConnectionAngularHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarJetConnectionAngularHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hd := scalarStateDPower_uniformTameGerm hD hT hS v0 (-(1 / 2))
  have hc := scalarStateConnectionFactor_uniformTameGerm hD hT hS v0
  have ha := (scalarStateAngularHeight_uniformTameGerm hD hT hS
    (scalarStateCenter S v0)).scalarStateSlopeAct hD hT hS
  exact hd.add (hc.scalarHeightUnitalAct ha hT hS hp ht) hp ht

theorem scalarCandidateJets_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarOutputsGrading S 7) (scalarStateCenter S v0)
      (scalarCandidateJets hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hz : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateCenter S v0) (fun _ : ScalarWeightedState S => (0 : ScalarHeightSpace S)) :=
    uniformTameGerm_const ht (scalarStateCenter S v0) 0
  change UniformTameGerm (scalarStateGrading S)
    (fun s => ∑ i : Fin 7, (scalarFieldGrading S s).comp (LinearMap.proj i))
    (scalarStateCenter S v0) (fun x i => scalarCandidateJets hD hT hS x i)
  apply UniformTameGerm.pi hp ht
  intro i
  fin_cases i
  · exact (scalarStateRadialHeight_uniformTameGerm hD hT hS
      (scalarStateCenter S v0)).prodMk hz hp ht
  · exact hz.prodMk (scalarStateAngularPrimitive_uniformTameGerm hD hT hS
      (scalarStateCenter S v0)) hp ht
  · exact (scalarJetCoframeRadialHeight_uniformTameGerm hD hT hS v0).prodMk hz hp ht
  · exact hz.prodMk (scalarJetCoframeMixedPrimitive_uniformTameGerm hD hT hS v0) hp ht
  · exact (scalarJetCoframeAngularHeight_uniformTameGerm hD hT hS v0).prodMk hz hp ht
  · exact hz.prodMk (scalarJetConnectionRadialPrimitive_uniformTameGerm hD hT hS v0) hp ht
  · exact (scalarJetConnectionAngularHeight_uniformTameGerm hD hT hS v0).prodMk hz hp ht

theorem scalarStateMeanSquare_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarStateMeanSquare hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hm := scalarStateMeanCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  exact hm.scalarHeightUnitalMul hm hT hS hp ht

theorem scalarStateMeanFourth_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarStateMeanFourth hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hm := scalarStateMeanSquare_uniformTameGerm hD hT hS v0
  exact hm.scalarHeightUnitalMul hm hT hS hp ht

theorem scalarStateSigma_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarStateSigma hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact (scalarStateQPower_uniformTameGerm hD hT hS v0 (-1)).scalarHeightUnitalMul
    (scalarStateDPower_uniformTameGerm hD hT hS v0 (-(1 / 2))) hT hS hp ht

theorem scalarCoefficientAHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarCoefficientAHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hm := scalarStateMeanCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hq := scalarStateQuotientHeight_uniformTameGerm hD hT hS v0
  have hd := scalarStateDPower_uniformTameGerm hD hT hS v0 (-(3 / 2))
  exact ((hm.scalarHeightUnitalMul hq hT hS hp ht).scalarHeightUnitalMul hd hT hS hp ht).scalarReferenceW hD hT hS hp ht

theorem scalarCoefficientBPrimitive_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarCoefficientBPrimitive hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hd := scalarStateDPower_uniformTameGerm hD hT hS v0 (-(3 / 2))
  have hm := (scalarStateMixedPrimitive_uniformTameGerm hD hT hS
    (scalarStateCenter S v0)).scalarStateEnergyOddAct hD hT hS
  exact (hd.scalarHeightOddUnitalAct hm hT hS hp ht).neg hp ht

theorem scalarCoefficientQuadraticHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarCoefficientQuadraticHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hm := scalarStateMixedPrimitive_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hc := hm.scalarHeightAngularMul hm hT hS hp ht
  have hleft := hc.scalarReferenceInvW hD hT hS hp ht
  have hmiddle := (((scalarStateMeanSquare_uniformTameGerm hD hT hS v0).scalarHeightUnitalAct hc hT hS hp ht).scalarReferenceW hD hT hS hp ht).const_smul hp ht 2
  have hright := ((((scalarStateMeanFourth_uniformTameGerm hD hT hS v0).scalarHeightUnitalAct hc hT hS hp ht).scalarReferenceW hD hT hS hp ht).scalarReferenceW hD hT hS hp ht).scalarReferenceW hD hT hS hp ht
  exact (hleft.add hmiddle hp ht).add hright hp ht

theorem scalarCoefficientCHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarCoefficientCHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hm := scalarStateMeanCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hsigma := scalarStateSigma_uniformTameGerm hD hT hS v0
  have hmd := scalarStateMeanDerivCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hleft := ((hm.scalarHeightUnitalMul hsigma hT hS hp ht).scalarReferenceWDeriv hD hT hS hp ht).scalarReferenceInvRadius hD hT hS hp ht
  have hmiddle := ((hsigma.scalarHeightUnitalAct hmd hT hS hp ht).scalarReferenceW hD hT hS hp ht).scalarReferenceInvRadius hD hT hS hp ht
  have hi := scalarStateInverseMeanHeight_uniformTameGerm hD hT hS v0
  have hq := scalarStateQPower_uniformTameGerm hD hT hS v0 (-1)
  have hd := scalarStateDPower_uniformTameGerm hD hT hS v0 (-(3 / 2))
  have hc := scalarCoefficientQuadraticHeight_uniformTameGerm hD hT hS v0
  have hright := hi.scalarHeightUnitalAct
    (hq.scalarHeightUnitalAct (hd.scalarHeightUnitalAct hc hT hS hp ht) hT hS hp ht) hT hS hp ht
  exact (hleft.add hmiddle hp ht).add hright hp ht

theorem scalarCandidateCoefficients_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarOutputsGrading S 3) (scalarStateCenter S v0)
      (scalarCandidateCoefficients hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hz : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateCenter S v0) (fun _ : ScalarWeightedState S => (0 : ScalarHeightSpace S)) :=
    uniformTameGerm_const ht (scalarStateCenter S v0) 0
  change UniformTameGerm (scalarStateGrading S)
    (fun s => ∑ i : Fin 3, (scalarFieldGrading S s).comp (LinearMap.proj i))
    (scalarStateCenter S v0) (fun x i => scalarCandidateCoefficients hD hT hS x i)
  apply UniformTameGerm.pi hp ht
  intro i
  fin_cases i
  · exact (scalarCoefficientAHeight_uniformTameGerm hD hT hS v0).prodMk hz hp ht
  · exact hz.prodMk (scalarCoefficientBPrimitive_uniformTameGerm hD hT hS v0) hp ht
  · exact (scalarCoefficientCHeight_uniformTameGerm hD hT hS v0).prodMk hz hp ht

theorem scalarTypePerturbationHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarTypePerturbationHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hi := scalarStateInverseMeanHeight_uniformTameGerm hD hT hS v0
  have hq := scalarStateQPower_uniformTameGerm hD hT hS v0 (-1)
  have hsigma := hi.scalarHeightUnitalMul hq hT hS hp ht
  have hm := scalarStateMeanSquare_uniformTameGerm hD hT hS v0
  have hw := ((hm.scalarHeightUnitalMul hsigma hT hS hp ht).scalarReferenceW hD hT hS hp ht).scalarReferenceW hD hT hS hp ht
  exact (hsigma.add hw hp ht).scalarReferenceInvRadius hD hT hS hp ht

theorem scalarResidualNumeratorHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarResidualNumeratorHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have ha := scalarStateRadialCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hb := scalarStateRadialSecondCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hc := scalarStateAngularPrimitiveCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hd := scalarStateAngularRadialPrimitiveCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have he := scalarStateAngularSecondCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hlinear := ((ha.add he hp ht).scalarStateWDerivAct hD hT hS).add
    (hb.scalarStateWAct hD hT hS) hp ht
  have hfirst := (ha.add (he.scalarStateEnergyAct hD hT hS) hp ht).scalarHeightMul hb hT hS hp ht
  have hsecond := ((hd.scalarHeightAngularMul hd hT hS hp ht).scalarStateEnergyAct hD hT hS).scalarReferenceRadius hD hT hS hp ht
  have hthird := (((hc.scalarHeightAngularMul hc hT hS hp ht).sub (ha.scalarHeightMul he hT hS hp ht) hp ht).scalarStateWDerivAct hD hT hS).scalarStateWAct hD hT hS
  have hnonlinear := (hfirst.sub hsecond hp ht).add hthird hp ht
  exact hlinear.add
    ((scalarStateQProjection_uniformTameGerm S (scalarStateCenter S v0)).scalarHeightSMul hnonlinear hS hp ht) hp ht

theorem scalarCandidateResidual_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarCandidateResidual hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact (scalarStateDPower_uniformTameGerm hD hT hS v0 (-(3 / 2))).scalarHeightUnitalAct
    (scalarResidualNumeratorHeight_uniformTameGerm hD hT hS v0) hT hS hp ht

end ContinuousFlexibility.Statements
