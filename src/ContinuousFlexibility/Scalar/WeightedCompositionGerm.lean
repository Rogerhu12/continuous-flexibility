import ContinuousFlexibility.Scalar.WeightedCompositionMaps
import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-!
# Canonical actual scalar composition and its uniform tame germ

The operation is the unique lift of the literal decoded scalar composition
on the whole height space.  The fixed-neighborhood composition theorem gives
its genuine uniform tower near zero by decoder injectivity.  This canonical
operation can then be composed with actual state germs vanishing at their
center, including smooth cutoff extensions of scalar powers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- The canonical lift of the globally defined actual decoded composition. -/
def weightedCompositionMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) (u : A.Space) : A.Space :=
  liftHeight hA (fun p => F (A.decode u p))
    (weightedComposition_heightMember hT hA hinterp hγ hF hF0 u)

theorem decode_weightedCompositionMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) (u : A.Space) :
    A.decode (weightedCompositionMap hT hA hinterp hγ hF hF0 u) =
      fun p => F (A.decode u p) :=
  decode_liftHeight hA _ _

theorem weightedCompositionMap_zero
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) :
    weightedCompositionMap hT hA hinterp hγ hF hF0 0 = 0 := by
  apply hA.2.2.2.2.2.1
  rw [decode_weightedCompositionMap, map_zero]
  funext p
  simp only [map_zero, Pi.zero_apply, hF0]

end SobolevModelData

/-- The globally defined canonical lift has one fixed-loss actual tower on
one neighborhood of zero in the physical height space. -/
theorem weightedCompositionMap_uniformTameGerm
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) :
    UniformTameGerm (S.height γ).grading (S.height γ).grading 0
      (SobolevModelData.weightedCompositionMap hT (hS.1 γ)
        ((hS.2.2.2.1 γ).2.2) hγ hF hF0) := by
  obtain ⟨base, loss, ε, hε, f, hfdecode, hftame⟩ :=
    exists_fixedNeighborhood_weightedComposition hT hS hγ hF hF0
  have hcanonical : FixedNeighborhoodSmoothTame
      (S.height γ).grading (S.height γ).grading
      {u | (S.height γ).grading base u < ε} base loss
      (SobolevModelData.weightedCompositionMap hT (hS.1 γ)
        ((hS.2.2.2.1 γ).2.2) hγ hF hF0) := by
    apply hftame.congr
    intro u hu
    apply (hS.1 γ).2.2.2.2.2.1
    exact (funext (hfdecode u hu)).trans
      (SobolevModelData.decode_weightedCompositionMap hT (hS.1 γ)
        ((hS.2.2.2.1 γ).2.2) hγ hF hF0 u).symm
  refine ⟨base, loss, ε, hε, ?_⟩
  simpa only [sub_zero] using hcanonical

section StateComposition

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X}
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {γ : ℝ} {f : X → (S.height γ).Space}

/-- A state germ which vanishes at its center admits every globally smooth
scalar composition vanishing at zero.  The output is the canonical actual
decoded map, and the source may be the prescribed nested scalar state. -/
theorem UniformTameGerm.weightedComposition
    (hf : UniformTameGerm p (S.height γ).grading x0 f) (hf0 : f x0 = 0)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (S.height γ).grading x0
      (fun x => SobolevModelData.weightedCompositionMap hT (hS.1 γ)
        ((hS.2.2.2.1 γ).2.2) hγ hF hF0 (f x)) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : ∀ n, CompleteSpace ((S.height γ).level n) :=
    fun n => SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 γ) n
  have houter : UniformTameGerm (S.height γ).grading (S.height γ).grading (f x0)
      (SobolevModelData.weightedCompositionMap hT (hS.1 γ)
        ((hS.2.2.2.1 γ).2.2) hγ hF hF0) := by
    rw [hf0]
    exact weightedCompositionMap_uniformTameGerm hT hS hγ hF hF0
  simpa only [Function.comp_def] using hf.comp houter hp ht (gradedSeminorm_monotone _ _)

end StateComposition

end ContinuousFlexibility.Statements
