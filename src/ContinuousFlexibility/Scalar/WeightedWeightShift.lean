module

public import ContinuousFlexibility.Scalar.WeightedWeightShiftJets
public import ContinuousFlexibility.Scalar.WeightedJetNorm
public import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# Continuous linear inclusions between the actual weighted height spaces

Lowering a weight exponent preserves every physical norm up to a constant at
that same order.  The frozen Sobolev decoder therefore lifts the inclusion to
a genuine continuous linear map, with zero loss and zero base, on the actual
projective spaces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The finite physical norm retains its exact order under a nonnegative
weight shift; the constant is independent of the height. -/
theorem physicalNorm_weight_shift_bound
    {D : ReferenceData} {T : MaterialData} {γ γ' : ℝ}
    (hT : IsMaterialData D T) (hγ : γ' ≤ γ) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      physicalNorm T γ' s f ≤ C * physicalNorm T γ s f := by
  classical
  have hjets (j : JetIndex s) := weightedPhysicalJet_weight_shift_bound hT hγ
    (j.val 0).val (j.val 1).val (j.val 2).val
  choose B hB hBx using hjets
  let K : ℝ := ∑ j, B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hB j)
  have hBK (j : JetIndex s) : B j ≤ K :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, ?_⟩
  intro f hf
  have hf' := heightMember_weight_shift hT hγ hf
  have hN : 0 ≤ physicalNorm T γ s f := Real.sqrt_nonneg _
  have hbound (a b c : ℕ) (horder : a + b + c ≤ s) :
      (eLpNorm (weightedPhysicalJet T γ' a b c f) 2 materialCylinderMeasure).toReal ≤
        K * physicalNorm T γ s f := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hj :
        (eLpNorm (weightedPhysicalJet T γ' a b c f) 2 materialCylinderMeasure).toReal ≤
          B j * physicalNorm T γ (a + b + c) f := by
      simpa [j] using (hBx j f hf).2
    exact hj.trans ((mul_le_mul_of_nonneg_left
      (physicalNorm_monotone_of_heightMember hf horder) (hB j)).trans
        (mul_le_mul_of_nonneg_right (hBK j) hN))
  exact (physicalNorm_le_of_weightedJet_bounds (mul_nonneg hK hN)
    (fun a b c _ => hf'.2.2.2.2 a b c) hbound).trans_eq (by ring)

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ γ' : ℝ}
  {A B : SobolevModelData}

private theorem weightShift_physical_bound
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (hγ : γ' ≤ γ) :
    ∀ s : ℕ, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space,
      physicalNorm T γ' s (A.decode u) ≤ C * A.grading (s + 0) u := by
  intro s _
  obtain ⟨C, hC, hCf⟩ := physicalNorm_weight_shift_bound hT hγ s
  refine ⟨C, hC, fun u => ?_⟩
  have h := hCf (A.decode u) (hA.2.2.2.1 u)
  rw [← sobolevGrading_eq_physicalNorm hA u s] at h
  simpa only [Nat.add_zero] using h

/-- The actual inclusion of a stronger weight into a weaker weight. -/
def weightShift (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T γ' B) (hγ : γ' ≤ γ) : A.Space →L[ℝ] B.Space :=
  liftCLM hB A.decode (fun u => heightMember_weight_shift hT hγ (hA.2.2.2.1 u))
    (withSeminorms_graded (fun n => A.level n) A.bond) (weightShift_physical_bound hT hA hγ)

theorem decode_weightShift (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T γ' B) (hγ : γ' ≤ γ) (u : A.Space) :
    B.decode (weightShift hT hA hB hγ u) = A.decode u :=
  decode_liftCLM hB A.decode (fun u => heightMember_weight_shift hT hγ (hA.2.2.2.1 u))
    (withSeminorms_graded (fun n => A.level n) A.bond) (weightShift_physical_bound hT hA hγ) u

theorem weightShift_isTame (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T γ' B) (hγ : γ' ≤ γ) :
    IsTameLinear A.grading B.grading (weightShift hT hA hB hγ).toLinearMap 0 0 :=
  liftLinear_isTame hB A.decode (fun u => heightMember_weight_shift hT hγ (hA.2.2.2.1 u))
    (weightShift_physical_bound hT hA hγ)

theorem weightShift_injective (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T γ' B) (hγ : γ' ≤ γ) :
    Function.Injective (weightShift hT hA hB hγ) := by
  intro u v huv
  apply hA.2.2.2.2.2.1
  rw [← decode_weightShift hT hA hB hγ u, ← decode_weightShift hT hA hB hγ v, huv]

theorem weightShift_fixedNeighborhoodSmoothTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T γ' B) (hγ : γ' ≤ γ)
    {U : Set A.Space} (hU : IsOpen U) :
    FixedNeighborhoodSmoothTame A.grading B.grading U 0 0 (weightShift hT hA hB hγ) :=
  (fixedNeighborhoodSmoothTame_continuousLinear (weightShift hT hA hB hγ)
    (weightShift_isTame hT hA hB hγ)).restrict hU (subset_univ U)

end SobolevModelData

end ContinuousFlexibility.Statements
