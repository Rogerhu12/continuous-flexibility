import ContinuousFlexibility.Analysis.N08RadialFamilyHeightBounds
import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# Exact Sobolev realization of a decaying radial linear family

The field is lifted through the actual decoder after proving its physical
membership and all norm bounds. This applies equally to a scalar cutoff
direction, a weak control vector, or their product.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {A : SobolevModelData}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def n08RadialFieldCLM (L : E →L[ℝ] (ℝ → ℝ)) : E →L[ℝ] (PolarPoint → ℝ) :=
  ContinuousLinearMap.pi (fun p => (ContinuousLinearMap.proj p.1).comp L)

theorem n08RadialFieldCLM_apply (L : E →L[ℝ] (ℝ → ℝ)) (u : E) (p : PolarPoint) :
    n08RadialFieldCLM L u p = L u p.1 := rfl

theorem n08_normGrading_topology : WithSeminorms (fun _ : ℕ => normSeminorm ℝ E) := by
  apply (norm_withSeminorms ℝ E).congr
  · intro n
    exact ⟨{()}, 1, by simp⟩
  · intro u
    exact ⟨{0}, 1, by simp⟩

variable (hT : IsMaterialData D T) (hA : IsSobolevModel D T n08WeakControlWeight A)
  (L : E →L[ℝ] (ℝ → ℝ))
  (hL : ∀ u, ContDiffOn ℝ ∞ (L u) (Ioo D.a D.b))
  (hzero : ∀ u r, r ∉ Ioo D.a D.b → L u r = 0)
  (hbound : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
    |iteratedDeriv s (L u) r| ≤ K * ‖u‖ * T.H r ^ (3 / 128 : ℝ) * T.M r)

private theorem n08_radialLift_member (u : E) :
    HeightMember D T n08WeakControlWeight (n08RadialFieldCLM L u) :=
  n08RadialFamilyField_heightMember hT hL hbound hzero u

private theorem n08_radialLift_bound :
    ∀ s : ℕ, 0 ≤ s → ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E,
      physicalNorm T n08WeakControlWeight s (n08RadialFieldCLM L u) ≤
        K * (normSeminorm ℝ E) u := by
  intro s _
  exact n08RadialFamilyField_physicalNorm_bound hT hL hbound s

/-- A genuine continuous linear map to the physical weighted height model. -/
def n08RadialFamilyLift : E →L[ℝ] A.Space :=
  SobolevModelData.liftCLM hA (n08RadialFieldCLM L).toLinearMap
    (n08_radialLift_member hT L hL hzero hbound)
    (p := fun _ : ℕ => normSeminorm ℝ E) (base := 0) (loss := 0)
    n08_normGrading_topology (n08_radialLift_bound hT L hL hbound)

theorem n08RadialFamilyLift_decode (u : E) (p : PolarPoint) :
    A.decode (n08RadialFamilyLift hT hA L hL hzero hbound u) p = L u p.1 := by
  rw [n08RadialFamilyLift, SobolevModelData.decode_liftCLM]
  rfl

theorem n08RadialFamilyLift_grading_bound (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E,
      A.grading s (n08RadialFamilyLift hT hA L hL hzero hbound u) ≤ K * ‖u‖ := by
  obtain ⟨K, hK, hKb⟩ := n08RadialFamilyField_physicalNorm_bound hT hL hbound s
  refine ⟨K, hK, fun u => ?_⟩
  rw [sobolevGrading_eq_physicalNorm hA]
  have he : A.decode (n08RadialFamilyLift hT hA L hL hzero hbound u) =
      n08RadialFamilyField (fun v => L v) u :=
    funext fun p => n08RadialFamilyLift_decode hT hA L hL hzero hbound u p
  rw [he]
  exact hKb u

theorem n08RadialFamilyLift_isTame :
    IsTameLinear (fun _ : ℕ => normSeminorm ℝ E) A.grading
      (n08RadialFamilyLift hT hA L hL hzero hbound).toLinearMap 0 0 := by
  intro s _
  obtain ⟨K, hK, hKb⟩ := n08RadialFamilyLift_grading_bound hT hA L hL hzero hbound s
  exact ⟨⟨K, hK⟩, hKb⟩

end ContinuousFlexibility.Statements
