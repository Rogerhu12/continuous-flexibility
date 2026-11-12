import ContinuousFlexibility.Scalar.WeightedDecodeLift
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact changes of weight for the physical models

Multiplication by the ratio of two positive material weights identifies their
normalized physical jets exactly. The map below changes the decoded field as
well as the model; it is distinct from the inclusion that keeps a field fixed
and lowers its weight. This permits products with unequal input weights to be
reduced to the existing sum-weight product estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n08WeightConjugationField (T : MaterialData) (γ δ : ℝ) :
    (PolarPoint → ℝ) →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun f p := T.H p.1 ^ (δ - γ) * f p
  map_add' f g := by funext p; exact mul_add _ _ _
  map_smul' c f := by
    funext p
    change T.H p.1 ^ (δ - γ) * (c * f p) = c * (T.H p.1 ^ (δ - γ) * f p)
    ring

theorem n08WeightConjugationField_apply (T : MaterialData) (γ δ : ℝ)
    (f : PolarPoint → ℝ) (p : PolarPoint) :
    n08WeightConjugationField T γ δ f p = T.H p.1 ^ (δ - γ) * f p := rfl

theorem n08WeightConjugationField_pullback {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (γ δ : ℝ) (f : PolarPoint → ℝ) :
    materialPullback T δ (n08WeightConjugationField T γ δ f) = materialPullback T γ f := by
  obtain ⟨_, hpos, _, _, _, _, _, hinv, _⟩ := hT
  funext p
  have hH := (hpos _ (hinv p.1).1).2.1
  change T.H (T.radius p.1) ^ (-δ) *
      (T.H (T.radius p.1) ^ (δ - γ) * f (T.radius p.1, p.2)) =
    T.H (T.radius p.1) ^ (-γ) * f (T.radius p.1, p.2)
  rw [← mul_assoc, ← Real.rpow_add hH, show -δ + (δ - γ) = -γ by ring]

theorem n08WeightConjugationField_jet {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (γ δ : ℝ) (f : PolarPoint → ℝ) (a b c : ℕ) :
    weightedPhysicalJet T δ a b c (n08WeightConjugationField T γ δ f) =
      weightedPhysicalJet T γ a b c f := by
  unfold weightedPhysicalJet
  rw [n08WeightConjugationField_pullback hT]

theorem n08WeightConjugationField_norm {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (γ δ : ℝ) (f : PolarPoint → ℝ) (s : ℕ) :
    physicalNorm T δ s (n08WeightConjugationField T γ δ f) = physicalNorm T γ s f := by
  unfold physicalNorm
  simp only [n08WeightConjugationField_jet hT]

theorem n08WeightConjugationField_member {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ δ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) :
    HeightMember D T δ (n08WeightConjugationField T γ δ f) := by
  have hH : ContDiffOn ℝ ∞ (fun p : PolarPoint => T.H p.1) (annularOpen D) :=
    (hT.1 T.H (by simp)).comp contDiffOn_fst (fun _ hp => hp.1)
  have hHne : ∀ p ∈ annularOpen D, T.H p.1 ≠ 0 :=
    fun p hp => ((hT.2.1 _ hp.1).2.1).ne'
  refine ⟨(hH.rpow_const_of_ne hHne).mul hf.1, ?_, ?_, ?_, ?_⟩
  · intro r θ
    change T.H r ^ (δ - γ) * f (r, -θ) = T.H r ^ (δ - γ) * f (r, θ)
    rw [hf.2.1 r θ]
  · intro p
    change T.H (p.1 + 0) ^ (δ - γ) * f (p + (0, Real.pi)) =
      T.H p.1 ^ (δ - γ) * f p
    rw [add_zero, hf.2.2.1 p]
  · intro p hp
    rw [n08WeightConjugationField_apply, hf.2.2.2.1 p hp, mul_zero]
  · intro a b c
    rw [n08WeightConjugationField_jet hT]
    exact hf.2.2.2.2 a b c

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ δ : ℝ} {A B : SobolevModelData}

private theorem n08_weightConjugation_bound (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) :
    ∀ s : ℕ, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space,
      physicalNorm T δ s ((n08WeightConjugationField T γ δ).comp A.decode u) ≤
        C * A.grading (s + 0) u := by
  intro s _
  refine ⟨1, zero_le_one, fun u => ?_⟩
  rw [LinearMap.comp_apply, n08WeightConjugationField_norm hT,
    one_mul, Nat.add_zero, sobolevGrading_eq_physicalNorm hA]

def n08WeightConjugation (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T δ B) : A.Space →L[ℝ] B.Space :=
  liftCLM hB ((n08WeightConjugationField T γ δ).comp A.decode)
    (fun u => n08WeightConjugationField_member hT (hA.2.2.2.1 u))
    (withSeminorms_graded (fun n => A.level n) A.bond)
    (n08_weightConjugation_bound hT hA)

theorem n08WeightConjugation_decode (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hB : IsSobolevModel D T δ B) (u : A.Space) :
    B.decode (n08WeightConjugation hT hA hB u) =
      n08WeightConjugationField T γ δ (A.decode u) :=
  decode_liftCLM hB ((n08WeightConjugationField T γ δ).comp A.decode)
    (fun v => n08WeightConjugationField_member hT (hA.2.2.2.1 v))
    (withSeminorms_graded (fun n => A.level n) A.bond)
    (n08_weightConjugation_bound hT hA) u

theorem n08WeightConjugation_grading (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hB : IsSobolevModel D T δ B)
    (u : A.Space) (s : ℕ) :
    B.grading s (n08WeightConjugation hT hA hB u) = A.grading s u := by
  rw [sobolevGrading_eq_physicalNorm hB, n08WeightConjugation_decode,
    n08WeightConjugationField_norm hT, sobolevGrading_eq_physicalNorm hA]

theorem n08WeightConjugation_isTame (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hB : IsSobolevModel D T δ B) :
    IsTameLinear A.grading B.grading (n08WeightConjugation hT hA hB).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun u => ?_⟩
  change B.grading s (n08WeightConjugation hT hA hB u) ≤ _
  rw [n08WeightConjugation_grading]
  simp only [NNReal.coe_one, one_mul, Nat.add_zero, le_refl]

end SobolevModelData

end ContinuousFlexibility.Statements
