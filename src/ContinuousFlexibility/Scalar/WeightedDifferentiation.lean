module

public import ContinuousFlexibility.Scalar.WeightedDifferentiationJets
public import ContinuousFlexibility.Scalar.WeightedDifferentiationAlgebra
public import ContinuousFlexibility.Scalar.WeightedJetNorm

/-!
# The actual radial derivative as a tame continuous linear map

The fixed loss of two in the weighted jet estimate is summed in the
physical norm and transferred through the original Sobolev decoder.
Every real weight exponent has the same base zero and loss two.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

theorem physicalNorm_radialPartial_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (hT : IsMaterialData D T) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      physicalNorm T γ s (radialPartial f) ≤ C * physicalNorm T γ (s + 2) f := by
  classical
  have hjets (j : JetIndex s) := weightedPhysicalJet_radialPartial_bound (γ := γ) hT
    (j.val 0).val (j.val 1).val (j.val 2).val
  choose B hB hBx using hjets
  let K : ℝ := ∑ j, B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hB j)
  have hBK (j : JetIndex s) : B j ≤ K :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, fun f hf => ?_⟩
  have hrad := heightMember_radialPartial hT hf
  have hN : 0 ≤ physicalNorm T γ (s + 2) f := Real.sqrt_nonneg _
  have hbound (a b c : ℕ) (horder : a + b + c ≤ s) :
      (eLpNorm (weightedPhysicalJet T γ a b c (radialPartial f))
        2 materialCylinderMeasure).toReal ≤ K * physicalNorm T γ (s + 2) f := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hj : (eLpNorm (weightedPhysicalJet T γ a b c (radialPartial f))
        2 materialCylinderMeasure).toReal ≤ B j * physicalNorm T γ (a + b + c + 2) f := by
      simpa [j] using (hBx j f hf).2
    exact hj.trans ((mul_le_mul_of_nonneg_left
      (physicalNorm_monotone_of_heightMember hf (by omega)) (hB j)).trans
        (mul_le_mul_of_nonneg_right (hBK j) hN))
  exact (physicalNorm_le_of_weightedJet_bounds (mul_nonneg hK hN)
    (fun a b c _ => hrad.2.2.2.2 a b c) hbound).trans_eq (by ring)

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

private theorem radial_heightMember
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (u : A.Space) :
    HeightMember D T γ (radialFieldLinear hA u) := by
  rw [radialFieldLinear_apply]
  exact heightMember_radialPartial hT (hA.2.2.2.1 u)

private theorem radial_physicalBound
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) :
    ∀ s, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space,
      physicalNorm T γ s (radialFieldLinear hA u) ≤ C * A.grading (s + 2) u := by
  intro s _
  obtain ⟨C, hC, hCf⟩ := physicalNorm_radialPartial_bound (γ := γ) hT s
  refine ⟨C, hC, fun u => ?_⟩
  simpa only [radialFieldLinear_apply, sobolevGrading_eq_physicalNorm hA] using
    hCf (A.decode u) (hA.2.2.2.1 u)

/-- The ordinary physical radial derivative on the actual projective space. -/
def radialCLM (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) :
    A.Space →L[ℝ] A.Space :=
  liftCLM hA (radialFieldLinear hA) (radial_heightMember hT hA)
    (withSeminorms_graded (fun n => A.level n) A.bond) (radial_physicalBound hT hA)

theorem decode_radialCLM
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (u : A.Space) :
    A.decode (radialCLM hT hA u) = radialPartial (A.decode u) :=
  decode_liftCLM hA (radialFieldLinear hA) (radial_heightMember hT hA)
    (withSeminorms_graded (fun n => A.level n) A.bond) (radial_physicalBound hT hA) u

theorem radialCLM_isTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) :
    IsTameLinear A.grading A.grading (radialCLM hT hA).toLinearMap 2 0 :=
  liftLinear_isTame hA (radialFieldLinear hA) (radial_heightMember hT hA)
    (radial_physicalBound hT hA)

theorem radialCLM_fixedNeighborhoodSmoothTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    {U : Set A.Space} (hU : IsOpen U) :
    FixedNeighborhoodSmoothTame A.grading A.grading U 0 2 (radialCLM hT hA) :=
  liftCLM_fixedNeighborhoodSmoothTame hA (radialFieldLinear hA) (radial_heightMember hT hA)
    (withSeminorms_graded (fun n => A.level n) A.bond) (radial_physicalBound hT hA) hU

end SobolevModelData

end ContinuousFlexibility.Statements
