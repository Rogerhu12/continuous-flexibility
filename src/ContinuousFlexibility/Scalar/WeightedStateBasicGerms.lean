import ContinuousFlexibility.Scalar.WeightedStateBasicFields
import ContinuousFlexibility.Scalar.WeightedOddHeightGerms
import ContinuousFlexibility.Scalar.WeightedHeightSmallness

/-!
# Uniform tame germs of the actual basic scalar state fields

These proofs apply the fixed-loss calculus to the literal candidate
expressions.  The four decoded scalar ranges used by the power extensions
are simultaneously small on one neighborhood of the prescribed center.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

section Actions

variable {x0 : ScalarWeightedState S} {f : ScalarWeightedState S → ScalarHeightSpace S}

theorem UniformTameGerm.scalarStateWAct
    (hf : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (fun x => scalarStateWAct hD hT hS x (f x)) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact ((scalarStateMeanCLM_uniformTameGerm hD hT hS x0).scalarHeightUnitalAct
    hf hT hS hp ht).scalarReferenceW hD hT hS hp ht

theorem UniformTameGerm.scalarStateWOddAct
    (hf : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (fun x => scalarStateWOddAct hD hT hS x (f x)) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  exact ((scalarStateMeanCLM_uniformTameGerm hD hT hS x0).scalarHeightOddUnitalAct
    hf hT hS hp ht).scalarReferenceW hD hT hS hp ht

theorem UniformTameGerm.scalarStateEnergyAct
    (hf : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (fun x => scalarStateEnergyAct hD hT hS x (f x)) := by
  exact hf.add
    ((hf.scalarStateWAct hD hT hS).scalarStateWAct hD hT hS)
    (scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)

theorem UniformTameGerm.scalarStateEnergyOddAct
    (hf : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (fun x => scalarStateEnergyOddAct hD hT hS x (f x)) := by
  exact hf.add
    ((hf.scalarStateWOddAct hD hT hS).scalarStateWOddAct hD hT hS)
    (scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)

end Actions

theorem scalarStateRadialHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateRadialHeight hD hT hS) := by
  exact (scalarStateQProjection_uniformTameGerm S x0).scalarHeightSMul
    (scalarStateRadialCLM_uniformTameGerm hD hT hS x0) hS
    (scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)

theorem scalarStateAngularPrimitive_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateAngularPrimitive hD hT hS) := by
  exact (scalarStateQProjection_uniformTameGerm S x0).scalarHeightSMul
    (scalarStateAngularPrimitiveCLM_uniformTameGerm hD hT hS x0) hS
    (scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)

theorem scalarStateMixedPrimitive_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateMixedPrimitive hD hT hS) := by
  exact (scalarStateQProjection_uniformTameGerm S x0).scalarHeightSMul
    (scalarStateAngularRadialPrimitiveCLM_uniformTameGerm hD hT hS x0) hS
    (scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)

theorem scalarStateAngularHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateAngularHeight hD hT hS) := by
  exact (scalarStateQProjection_uniformTameGerm S x0).scalarHeightSMul
    (scalarStateAngularSecondCLM_uniformTameGerm hD hT hS x0) hS
    (scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)

theorem scalarStateAngularSquare_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateAngularSquare hD hT hS) := by
  have hf := scalarStateAngularPrimitive_uniformTameGerm hD hT hS x0
  exact hf.scalarHeightAngularMul hf hT hS
    (scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)

theorem scalarStateDiscriminantHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x0 : ScalarWeightedState S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) x0
      (scalarStateDiscriminantHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have ha := scalarStateRadialHeight_uniformTameGerm hD hT hS x0
  have hb := scalarStateAngularSquare_uniformTameGerm hD hT hS x0
  exact (((ha.scalarStateWAct hD hT hS).const_smul hp ht (-2)).sub
    (ha.scalarHeightMul ha hT hS hp ht) hp ht).sub
      (hb.scalarStateEnergyAct hD hT hS) hp ht

theorem scalarStateInverseMeanHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarStateInverseMeanHeight hD hT hS) := by
  exact (scalarStateMeanCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)).scalarHeightPower
    (scalarStateMeanCLM_center hD hT hS v0) hT hS (-1)
    (scalarStateGrading_monotone S) (weighted_scalarStateGrading_withSeminorms S)

theorem scalarStateQuotientHeight_uniformTameGerm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S) (scalarStateCenter S v0)
      (scalarStateQuotientHeight hD hT hS) := by
  have hp := scalarStateGrading_monotone S
  have ht := weighted_scalarStateGrading_withSeminorms S
  have hi := scalarStateInverseMeanHeight_uniformTameGerm hD hT hS v0
  have ha := scalarStateRadialHeight_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  have hb := scalarStateAngularHeight_uniformTameGerm hD hT hS (scalarStateCenter S v0)
  exact (hi.scalarHeightUnitalAct (ha.add (hb.scalarStateEnergyAct hD hT hS) hp ht)
    hT hS hp ht).scalarReferenceInvW hD hT hS hp ht

/-- All four scalar power ranges are controlled at every physical point on
one neighborhood of the actual state center. -/
theorem eventually_scalarCandidatePowerBounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (v0 : ScalarHeightSpace S) :
    ∀ᶠ x in 𝓝 (scalarStateCenter S v0), ScalarCandidatePowerBounds hD hT hS x := by
  have hm := (scalarStateMeanCLM_uniformTameGerm hD hT hS (scalarStateCenter S v0)).scalarDecode_small
    hD hT hS (scalarStateMeanCLM_center hD hT hS v0) (by norm_num : 0 < (1 / 2 : ℝ))
  have hd := (scalarStateDiscriminantHeight_uniformTameGerm hD hT hS
    (scalarStateCenter S v0)).scalarDecode_small hD hT hS
      (scalarStateDiscriminantHeight_center hD hT hS v0) (by norm_num : 0 < (1 / 2 : ℝ))
  have ha := (scalarStateAngularSquare_uniformTameGerm hD hT hS
    (scalarStateCenter S v0)).scalarDecode_small hD hT hS
      (scalarStateAngularSquare_center hD hT hS v0) (by norm_num : 0 < (1 / 2 : ℝ))
  have hq := (scalarStateQuotientHeight_uniformTameGerm hD hT hS v0).scalarDecode_small
    hD hT hS (scalarStateQuotientHeight_center hD hT hS v0) (by norm_num : 0 < (1 / 2 : ℝ))
  filter_upwards [hm, hd, ha, hq] with x hmx hdx hax hqx
  exact ⟨fun z => (hmx z).le, fun z => (hdx z).le,
    fun z => (hax z).le, fun z => (hqx z).le⟩

end ContinuousFlexibility.Statements
