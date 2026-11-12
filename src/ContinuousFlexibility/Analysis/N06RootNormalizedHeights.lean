import ContinuousFlexibility.Scalar.WeightedCommonHeightCalculus
import ContinuousFlexibility.Scalar.WeightedStateTopology
import ContinuousFlexibility.Analysis.N06NuSpatialCalculus
import ContinuousFlexibility.Analysis.NeighborhoodStateBounds

/-!
# Actual reference-normalized root height fields

The reciprocal reference profile is used through its already constructed
weighted multiplier. Thus all four root inputs are genuine decoded fields
of the original common height. The two odd fields are angular derivatives
of even decoded primitives. Their spatial jets have one fixed loss; no
pointwise lower bound for the flat reference profile is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n06RootNormalizedRadialCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  (scalarReferenceInvWCLM hD hT hS).comp (scalarCommonRadialCLM hD hT hS)

def n06RootAngularPrimitiveCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  (scalarStateAngularPrimitiveCLM hD hT hS).comp (scalarCommonDirectionCLM S)

def n06RootNormalizedMixedPrimitiveCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  (scalarReferenceInvWCLM hD hT hS).comp
    ((scalarStateAngularRadialPrimitiveCLM hD hT hS).comp (scalarCommonDirectionCLM S))

def n06RootNormalizedAngularSecondCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  (scalarReferenceInvWCLM hD hT hS).comp
    ((scalarStateAngularSecondCLM hD hT hS).comp (scalarCommonDirectionCLM S))

theorem n06RootNormalizedRadialCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarCommonHeightGrading S) (scalarHeightGrading S)
      (n06RootNormalizedRadialCLM hD hT hS).toLinearMap 3 0 :=
  (scalarReferenceInvWCLM_isTame hD hT hS).comp
    (scalarCommonRadialCLM_isTame hD hT hS)

theorem n06RootAngularPrimitiveCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarCommonHeightGrading S) (scalarHeightGrading S)
      (n06RootAngularPrimitiveCLM hD hT hS).toLinearMap 1 0 :=
  (scalarStateAngularPrimitiveCLM_isTame hD hT hS).comp
    (scalarCommonDirectionCLM_isTame S)

theorem n06RootNormalizedMixedPrimitiveCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarCommonHeightGrading S) (scalarHeightGrading S)
      (n06RootNormalizedMixedPrimitiveCLM hD hT hS).toLinearMap 4 0 :=
  (scalarReferenceInvWCLM_isTame hD hT hS).comp
    ((scalarStateAngularRadialPrimitiveCLM_isTame hD hT hS).comp
      (scalarCommonDirectionCLM_isTame S))

theorem n06RootNormalizedAngularSecondCLM_isTame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (scalarCommonHeightGrading S) (scalarHeightGrading S)
      (n06RootNormalizedAngularSecondCLM hD hT hS).toLinearMap 4 0 :=
  (scalarReferenceInvWCLM_isTame hD hT hS).comp
    ((scalarStateAngularSecondCLM_isTame hD hT hS).comp
      (scalarCommonDirectionCLM_isTame S))

theorem n06_decode_rootNormalizedRadial
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (u : ScalarCommonHeight S) (p : PolarPoint) :
    (S.height scalarBeta).decode (n06RootNormalizedRadialCLM hD hT hS u) p =
      (D.w p.1)⁻¹ * radialPartial (scalarCommonHeightDecode S u) p := by
  change (S.height scalarBeta).decode
    (scalarReferenceInvWCLM hD hT hS (scalarCommonRadialCLM hD hT hS u)) p = _
  rw [decode_scalarReferenceInvWCLM, decode_scalarCommonRadialCLM]

theorem n06_angularPartial_decode_rootAngularPrimitive
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (u : ScalarCommonHeight S) :
    angularPartial ((S.height scalarBeta).decode (n06RootAngularPrimitiveCLM hD hT hS u)) =
      heightAngular (scalarCommonHeightDecode S u) :=
  angularPartial_decode_scalarStateAngularPrimitiveCLM hD hT hS (scalarHeightDirection S u)

theorem n06_angularPartial_decode_invW
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (u : ScalarHeightSpace S) :
    angularPartial ((S.height scalarBeta).decode (scalarReferenceInvWCLM hD hT hS u)) =
      fun p => (D.w p.1)⁻¹ * angularPartial ((S.height scalarBeta).decode u) p := by
  have hf := (scalarHeight_decode_contDiff_and_flatJets hT hS u).1
  have hg := (scalarHeight_decode_contDiff_and_flatJets hT hS
    (scalarReferenceInvWCLM hD hT hS u)).1
  have he : (S.height scalarBeta).decode (scalarReferenceInvWCLM hD hT hS u) =
      fun p => (D.w p.1)⁻¹ * (S.height scalarBeta).decode u p :=
    funext (decode_scalarReferenceInvWCLM hD hT hS u)
  rw [he] at hg ⊢
  exact angularPartial_radialProduct_of_contDiff (k := fun r => (D.w r)⁻¹) hf hg

theorem n06_angularPartial_decode_rootNormalizedMixedPrimitive
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (u : ScalarCommonHeight S) :
    angularPartial ((S.height scalarBeta).decode
        (n06RootNormalizedMixedPrimitiveCLM hD hT hS u)) =
      fun p => (D.w p.1)⁻¹ * radialPartial (heightAngular (scalarCommonHeightDecode S u)) p := by
  change angularPartial ((S.height scalarBeta).decode
    (scalarReferenceInvWCLM hD hT hS
      (scalarStateAngularRadialPrimitiveCLM hD hT hS (scalarHeightDirection S u)))) = _
  rw [n06_angularPartial_decode_invW,
    angularPartial_decode_scalarStateAngularRadialPrimitiveCLM]
  rfl

theorem n06_decode_rootNormalizedAngularSecond
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (u : ScalarCommonHeight S) (p : PolarPoint) :
    (S.height scalarBeta).decode (n06RootNormalizedAngularSecondCLM hD hT hS u) p =
      (D.w p.1)⁻¹ * angularPartial (heightAngular (scalarCommonHeightDecode S u)) p := by
  change (S.height scalarBeta).decode
    (scalarReferenceInvWCLM hD hT hS
      (scalarStateAngularSecondCLM hD hT hS (scalarHeightDirection S u))) p = _
  rw [decode_scalarReferenceInvWCLM, decode_scalarStateAngularSecondCLM]
  rfl

private theorem n06_root_decoded_mixed_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ScalarHeightSpace S) p, p ∈ annularOpen D →
      |mixedDerivative a b ((S.height scalarBeta).decode u) p| ≤
        C * scalarHeightGrading S (a + b + 2) u := by
  obtain ⟨J, hJ, hj⟩ := scalarMixedDerivative_le_reference_grading hD hT hS a b
    (a + b + 2) le_rfl
  obtain ⟨M, hM, hm⟩ := referenceProfile_uniform_upper_bound hD
  refine ⟨J * M, mul_nonneg hJ hM, ?_⟩
  intro u p hp
  exact (hj u p hp).trans
    ((mul_le_mul_of_nonneg_left (hm p.1 hp.1)
      (mul_nonneg hJ (apply_nonneg _ _))).trans_eq (by ring))

/-- A single original height seminorm controls all physical spatial jets. -/
theorem n06_root_decoded_spatial_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ScalarHeightSpace S) k, k ≤ n →
      ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k ((S.height scalarBeta).decode u) p‖ ≤
        C * scalarHeightGrading S (n + 2) u := by
  classical
  let I := Fin (n + 1) × Fin (n + 1)
  have hchoices (i : I) := n06_root_decoded_mixed_bound hD hT hS i.1.val i.2.val
  choose c hc hbound using hchoices
  let A : ℝ := ∑ i : I, c i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hc i)
  refine ⟨(2 : ℝ) ^ n * A, mul_nonneg (by positivity) hA, ?_⟩
  intro u k hk p hp
  have hP : 0 ≤ scalarHeightGrading S (n + 2) u := apply_nonneg _ _
  have hm (a b : ℕ) (hab : a + b = k) :
      ‖mixedDerivative a b ((S.height scalarBeta).decode u) p‖ ≤
        A * scalarHeightGrading S (n + 2) u := by
    let i : I := (⟨a, by omega⟩, ⟨b, by omega⟩)
    have hi : c i ≤ A := Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
    have horder : i.1.val + i.2.val + 2 ≤ n + 2 := by
      change a + b + 2 ≤ n + 2
      omega
    exact (hbound i u p hp).trans
      ((mul_le_mul_of_nonneg_left
        (scalarHeightGrading_monotone S horder u) (hc i)).trans
          (mul_le_mul_of_nonneg_right hi hP))
  have hh := norm_iteratedFDeriv_le_of_mixedDerivative (isOpen_Ioo.prod isOpen_univ)
    (scalarHeight_decode_contDiff_and_flatJets hT hS u).1.contDiffOn k hp
    (mul_nonneg hA hP) hm
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
      (mul_nonneg hA hP)).trans_eq (mul_assoc _ _ _).symm)

/-- Angular differentiation of the even primitive costs exactly one
additional spatial derivative. -/
theorem n06_root_decoded_and_angular_spatial_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ScalarHeightSpace S) k, k ≤ n →
      ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k ((S.height scalarBeta).decode u) p‖ ≤
          C * scalarHeightGrading S (n + 3) u ∧
        ‖iteratedFDeriv ℝ k (angularPartial ((S.height scalarBeta).decode u)) p‖ ≤
          C * scalarHeightGrading S (n + 3) u := by
  obtain ⟨C, hC, hb⟩ := n06_root_decoded_spatial_bound hD hT hS (n + 1)
  refine ⟨C, hC, ?_⟩
  intro u k hk p hp
  have hs := (scalarHeight_decode_contDiff_and_flatJets hT hS u).1
  constructor
  · exact hb u k (by omega) p hp
  · have h := n06_norm_iteratedFDeriv_directional_le
      (isOpen_Ioo.prod isOpen_univ) hs.contDiffOn (0, 1) k hp
    have he : ‖((0, 1) : PolarPoint)‖ = 1 := by simp
    rw [he, mul_one] at h
    exact h.trans (hb u (k + 1) (by omega) p hp)

end ContinuousFlexibility.Statements
