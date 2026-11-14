module

public import ContinuousFlexibility.Analysis.N07aNuReducedSource
public import ContinuousFlexibility.Analysis.N04RealizationUniformDirection

/-!
# The actual reduced scalar residual on one uniform neighborhood

The scalar realization already supplies a uniform tower. Its composition
with the actual compact border parameter retains that tower before the
local smooth-tame wrapper forgets its fixed-domain estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- One neighborhood and one loss work for the entire actual residual
tower. The field is decoded as the literal border-state residual. -/
theorem n04Realization_exists_uniformNuReducedResidual
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D)
    (v₀ : ScalarHeightSpace S) :
    ∃ U : Set (N07aNuParameter S), IsOpen U ∧ n07aNuParameterCenter S v₀ ∈ U ∧
      ∃ base loss : ℕ, ∃ f : N07aNuParameter S → ScalarHeightSpace S,
        FixedNeighborhoodSmoothTame (n07aNuParameterGrading S)
          (scalarHeightGrading S) U base loss f ∧
        (∀ x ∈ U, ∀ p, (S.height scalarBeta).decode (f x) p =
          scalarStateResidual D S (n07aNuParameterState hT hS hb x) p) := by
  letI : IsTopologicalAddGroup (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (N07aNuParameter S) :=
    (n07aNuParameterGrading_withSeminorms S).continuousSMul
  letI : LocallyConvexSpace ℝ (ScalarWeightedState S) :=
    (weighted_scalarStateGrading_withSeminorms S).toLocallyConvexSpace
  letI : ∀ n, CompleteSpace ((S.height scalarBeta).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 scalarBeta) n
  let construction := scalarWeightedS05 D T S hD hT hS v₀
  let W : WeightedScalarData S := construction.choose
  have h03 : IsWeightedS03 D S v₀ W := construction.choose_spec.1
  have h04 : IsWeightedS04 D S v₀ W := construction.choose_spec.2.1
  let V : Set (ScalarWeightedState S) := scalarStateBall S v₀ W.base W.epsilon
  let J : SmoothDirections V W.residual := h04.2.2.choose
  have hJ : UniformScalarTowerEstimate (scalarStateGrading S) (scalarHeightGrading S)
      V W.base W.loss W.residual J := h04.2.2.choose_spec.1
  have hI := n07aNuParameterState_uniformTameGerm hT hS hb v₀
  have hR : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S)
      (n07aNuParameterState hT hS hb (n07aNuParameterCenter S v₀)) W.residual := by
    rw [n07aNuParameterState_center]
    exact (fixedNeighborhoodSmoothTame_of_uniform J hJ).uniformTameGerm
      (weighted_scalarStateGrading_monotone S)
      (weighted_scalarStateGrading_withSeminorms S) h03.2.2.2.1
  have hcomp := hI.comp hR (n07aNuParameterGrading_monotone S)
    (n07aNuParameterGrading_withSeminorms S) (weighted_scalarStateGrading_monotone S)
  obtain ⟨b, l, δ, hδ, hf⟩ := hcomp
  let U₀ : Set (N07aNuParameter S) :=
    {x | n07aNuParameterGrading S b (x - n07aNuParameterCenter S v₀) < δ}
  have hU₀ : IsOpen U₀ := isOpen_uniformTameBall
    (n07aNuParameterGrading_withSeminorms S) b _ δ
  have hc₀ : n07aNuParameterCenter S v₀ ∈ U₀ := by
    have hz : n07aNuParameterGrading S b (0 : N07aNuParameter S) = 0 :=
      (n07aNuParameterGrading S b).map_zero'
    simpa only [U₀, Set.mem_ofPred_eq, sub_self, hz] using hδ
  have hIV : n07aNuParameterState hT hS hb ⁻¹' V ∈
      𝓝 (n07aNuParameterCenter S v₀) := by
    apply hI.continuousAt.preimage_mem_nhds
    rw [n07aNuParameterState_center]
    exact h03.2.2.1.mem_nhds h03.2.2.2.1
  obtain ⟨c, η, _, hη, _, hsub⟩ := exists_small_uniformTameBall
    (n07aNuParameterGrading_monotone S) (n07aNuParameterGrading_withSeminorms S)
    (inter_mem (hU₀.mem_nhds hc₀) hIV) b
  let U : Set (N07aNuParameter S) :=
    {x | n07aNuParameterGrading S c (x - n07aNuParameterCenter S v₀) < η}
  have hU : IsOpen U := isOpen_uniformTameBall
    (n07aNuParameterGrading_withSeminorms S) c _ η
  refine ⟨U, hU, ?_, b, l, W.residual ∘ n07aNuParameterState hT hS hb,
    hf.restrict hU (fun x hx => (hsub hx).1), ?_⟩
  · have hz : n07aNuParameterGrading S c (0 : N07aNuParameter S) = 0 :=
      (n07aNuParameterGrading S c).map_zero'
    simpa only [U, Set.mem_ofPred_eq, sub_self, hz] using hη
  · intro x hx p
    exact h04.1 _ (hsub hx).2 p

end ContinuousFlexibility.Analysis
