import ContinuousFlexibility.Analysis.CoupledLogProfileWeakBounds
import ContinuousFlexibility.Analysis.CoupledRadialFamilyHeightBounds
import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# The actual logarithmic profile in a positive weighted height space

The pointwise linear logarithmic profile lifts through the original physical
decoder after its membership and fixed-loss physical estimates have been
proved. The construction works on the whole state space and vanishes at
the actual reference state.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def coupledLogProfileFieldCLM (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) :
    AnnularState S →L[ℝ] (PolarPoint → ℝ) :=
  ContinuousLinearMap.pi (fun p => coupled_logProfileEvalCLM hS hC p.1)

theorem coupledLogProfileFieldCLM_apply (hS : IsPhysicalSpaces D T S)
    (hC : controlGeometryConditions D S C) (v : AnnularState S) (p : PolarPoint) :
    coupledLogProfileFieldCLM hS hC v p = coupled_stateLogProfile D S C v p.1 :=
  coupled_logProfileEvalCLM_apply hS hC p.1 v

theorem coupled_logProfile_heightMember
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (v : AnnularState S) :
    HeightMember D T coupledWeakProfileWeight
      (coupledLogProfileFieldCLM hS hN.2.2.2.1 v) := by
  have hfield : coupledLogProfileFieldCLM hS hN.2.2.2.1 v =
      coupledRadialFamilyField (coupled_stateLogProfile D S C) v :=
    funext fun p => coupledLogProfileFieldCLM_apply hS hN.2.2.2.1 v p
  rw [hfield]
  exact coupledRadialFamilyField_heightMember hT
    (fun u => (coupled_contDiff_stateLogProfile hT hS hN u).contDiffOn)
    (P := fun n u => stateGrading S (n + (base + loss)) u)
    (fun n u => apply_nonneg _ _)
    (fun _ _ h u => solve_stateGrading_monotone S (Nat.add_le_add_right h _) u)
    (coupled_logProfile_decay_jet_bound hT hS hN)
    (fun u r hr => coupled_stateLogProfile_zero_off_core hN u hr) v

theorem coupled_logProfile_physicalNorm_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : AnnularState S,
      physicalNorm T coupledWeakProfileWeight s
          (coupledLogProfileFieldCLM hS hN.2.2.2.1 v) ≤
        K * stateGrading S (s + (base + loss)) v := by
  obtain ⟨K, hK, hKb⟩ := coupledRadialFamilyField_physicalNorm_bound hT
    (fun u => (coupled_contDiff_stateLogProfile hT hS hN u).contDiffOn)
    (P := fun n u => stateGrading S (n + (base + loss)) u)
    (fun n u => apply_nonneg _ _)
    (fun _ _ h u => solve_stateGrading_monotone S (Nat.add_le_add_right h _) u)
    (coupled_logProfile_decay_jet_bound hT hS hN) s
  refine ⟨K, hK, fun v => ?_⟩
  have hfield : coupledLogProfileFieldCLM hS hN.2.2.2.1 v =
      coupledRadialFamilyField (coupled_stateLogProfile D S C) v :=
    funext fun p => coupledLogProfileFieldCLM_apply hS hN.2.2.2.1 v p
  rw [hfield]
  exact hKb v

def coupledLogProfileLift
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    AnnularState S →L[ℝ] (S.height coupledWeakProfileWeight).Space :=
  SobolevModelData.liftCLM (hS.1 coupledWeakProfileWeight)
    (coupledLogProfileFieldCLM hS hN.2.2.2.1).toLinearMap
    (coupled_logProfile_heightMember hT hS hN)
    (p := stateGrading S) (base := 0) (loss := base + loss)
    (solve_stateGrading_withSeminorms S)
    (fun s _ => coupled_logProfile_physicalNorm_bound hT hS hN s)

theorem coupledLogProfileLift_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (v : AnnularState S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledLogProfileLift hT hS hN v) p =
      coupled_stateLogProfile D S C v p.1 := by
  rw [coupledLogProfileLift, SobolevModelData.decode_liftCLM]
  exact coupledLogProfileFieldCLM_apply hS hN.2.2.2.1 v p

theorem coupledLogProfileLift_isTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    IsTameLinear (stateGrading S) (S.height coupledWeakProfileWeight).grading
      (coupledLogProfileLift hT hS hN).toLinearMap (base + loss) 0 :=
  SobolevModelData.liftLinear_isTame (hS.1 coupledWeakProfileWeight)
    (coupledLogProfileFieldCLM hS hN.2.2.2.1).toLinearMap
    (coupled_logProfile_heightMember hT hS hN)
    (fun s _ => coupled_logProfile_physicalNorm_bound hT hS hN s)

theorem coupledLogProfileLift_fixedNeighborhoodSmoothTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {U : Set (AnnularState S)} (hU : IsOpen U) :
    FixedNeighborhoodSmoothTame (stateGrading S) (S.height coupledWeakProfileWeight).grading
      U 0 (base + loss) (coupledLogProfileLift hT hS hN) :=
  (fixedNeighborhoodSmoothTame_continuousLinear _
    (coupledLogProfileLift_isTame hT hS hN)).restrict hU (subset_univ U)

theorem coupledLogProfileLift_reference
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    coupledLogProfileLift hT hS hN C.referenceState = 0 := by
  apply (hS.1 coupledWeakProfileWeight).2.2.2.2.2.1
  funext p
  rw [coupledLogProfileLift_decode]
  simp only [coupled_stateLogProfile, hN.2.2.1.2.2.1, stateControlSum,
    coupled_stateKappa_reference hN.2.2.1, zero_mul, tsum_zero, zero_add,
    map_zero, Pi.zero_apply]

end ContinuousFlexibility.Statements
