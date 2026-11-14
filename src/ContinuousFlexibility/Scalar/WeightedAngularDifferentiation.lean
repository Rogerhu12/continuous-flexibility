module

public import ContinuousFlexibility.Scalar.WeightedDifferentiationAlgebra
public import ContinuousFlexibility.Scalar.WeightedJetNorm
public import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# The second angular derivative on the actual weighted spaces

Angular differentiation shifts the angular jet index by two. The resulting
map has one fixed loss of two and base zero, for every real weight exponent.
It is lifted through the given decoder and is continuous in the original
projective topology.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ}

theorem weightedPhysicalJet_angularPartial_twice_eq
    (hT : IsMaterialData D T) {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) (a b c : ℕ) :
    weightedPhysicalJet T γ a b c (angularPartial (angularPartial f)) =
      weightedPhysicalJet T γ a (b + 2) c f := by
  have hG := contDiff_materialPullback (γ := γ) hT hf.1
  have hfirst := scalar_contDiffOn_angularPartial isOpen_univ hG.contDiffOn
  funext p
  simp only [weightedPhysicalJet, materialPullback_angularPartial_twice (γ := γ) hT hf.1,
    mixedDerivative_angularPartial isOpen_univ hfirst a b (mem_univ p),
    mixedDerivative_angularPartial isOpen_univ hG.contDiffOn a (b + 1) (mem_univ p),
    Nat.add_assoc]

theorem heightMember_angularPartial_twice
    (hT : IsMaterialData D T) {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) :
    HeightMember D T γ (angularPartial (angularPartial f)) := by
  apply heightMember_angularPartial_twice_of_weightedJets hf
  intro a b c
  rw [weightedPhysicalJet_angularPartial_twice_eq hT hf]
  exact hf.2.2.2.2 a (b + 2) c

theorem physicalNorm_angularPartial_twice_le
    (hT : IsMaterialData D T) {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) (s : ℕ) :
    physicalNorm T γ s (angularPartial (angularPartial f)) ≤
      Real.sqrt (Fintype.card (JetIndex s) : ℝ) * physicalNorm T γ (s + 2) f := by
  apply physicalNorm_le_of_weightedJet_bounds (Real.sqrt_nonneg _)
  · intro a b c _
    rw [weightedPhysicalJet_angularPartial_twice_eq hT hf]
    exact hf.2.2.2.2 a (b + 2) c
  · intro a b c habc
    rw [weightedPhysicalJet_angularPartial_twice_eq hT hf]
    exact weightedPhysicalJet_norm_le_physicalNorm hf (by omega)

namespace SobolevModelData

variable {A : SobolevModelData}

private theorem angularSecond_heightMember
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (u : A.Space) :
    HeightMember D T γ (angularSecondFieldLinear hA u) := by
  rw [angularSecondFieldLinear_apply]
  exact heightMember_angularPartial_twice hT (hA.2.2.2.1 u)

private theorem angularSecond_physicalBound
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) :
    ∀ s, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space,
      physicalNorm T γ s (angularSecondFieldLinear hA u) ≤ C * A.grading (s + 2) u := by
  intro s _
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ), Real.sqrt_nonneg _, fun u => ?_⟩
  simpa only [angularSecondFieldLinear_apply, sobolevGrading_eq_physicalNorm hA] using
    physicalNorm_angularPartial_twice_le hT (hA.2.2.2.1 u) s

/-- The actual second angular derivative, in the original Sobolev model. -/
def angularSecondCLM
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) : A.Space →L[ℝ] A.Space :=
  liftCLM hA (angularSecondFieldLinear hA) (angularSecond_heightMember hT hA)
    (withSeminorms_graded (fun n => A.level n) A.bond) (angularSecond_physicalBound hT hA)

theorem decode_angularSecondCLM
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (u : A.Space) :
    A.decode (angularSecondCLM hT hA u) = angularPartial (angularPartial (A.decode u)) :=
  decode_liftCLM hA (angularSecondFieldLinear hA) (angularSecond_heightMember hT hA)
    (withSeminorms_graded (fun n => A.level n) A.bond) (angularSecond_physicalBound hT hA) u

theorem angularSecondCLM_isTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) :
    IsTameLinear A.grading A.grading (angularSecondCLM hT hA).toLinearMap 2 0 :=
  liftLinear_isTame hA (angularSecondFieldLinear hA) (angularSecond_heightMember hT hA)
    (angularSecond_physicalBound hT hA)

theorem angularSecondCLM_fixedNeighborhoodSmoothTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    {U : Set A.Space} (hU : IsOpen U) :
    FixedNeighborhoodSmoothTame A.grading A.grading U 0 2 (angularSecondCLM hT hA) :=
  liftCLM_fixedNeighborhoodSmoothTame hA (angularSecondFieldLinear hA)
    (angularSecond_heightMember hT hA)
    (withSeminorms_graded (fun n => A.level n) A.bond) (angularSecond_physicalBound hT hA) hU

end SobolevModelData

end ContinuousFlexibility.Statements
