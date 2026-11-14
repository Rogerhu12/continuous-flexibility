module

public import ContinuousFlexibility.Analysis.N01ReturnVelocitySmoothTame
public import ContinuousFlexibility.Analysis.NormedSmoothDirections

/-!
# Genuine circle calculus with arbitrary topological parameters

These operations retain actual directional towers. They do not require
a tame estimate for the parameter map being composed. This is useful
when a physical radius is one of the parameters and uniform estimates
are proved separately from the original mixed N01 bounds.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

section LinearRestriction

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
  {U : Set F} {V : Set E} {f : F → G}

def SmoothDirections.compLinear (J : SmoothDirections U f)
    (L : E →L[ℝ] F) (hV : IsOpen V) (hmap : MapsTo L V U) :
    SmoothDirections V (fun x => f (L x)) :=
  (J.compAffine L 0 hV (fun x hx => by simpa only [zero_add] using hmap hx)).congrOn
    (fun x _ => by simp only [zero_add])

end LinearRestriction

section LinearOn

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

def smoothDirectionsLinearOn (L : E →L[ℝ] F) {U : Set E} (hU : IsOpen U) :
    SmoothDirections U L :=
  (smoothDirectionsLinear L).compLinear (ContinuousLinearMap.id ℝ E) hU
    (fun _ _ => mem_univ _)

end LinearOn

section CircleComposition

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {V : Set F} {f : E → F} {g : F → H.Space}

def SmoothDirections.compCircle (J : SmoothDirections U f) (hH : IsCircleModel T γ H)
    (K : SmoothDirections V g) (hmap : MapsTo f U V) :
    SmoothDirections U (fun x => g (f x)) := by
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  exact smoothDirectionsOfJets J.open_domain
    (projectiveCompositionJets f J.D K.D)
    (HasProjectiveJetsOn.comp_topological J.open_domain K.open_domain
      J.hasProjectiveJetsOn K.hasProjectiveJetsOn hmap)

end CircleComposition

section Operations

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {f g : E → H.Space}

def circleProductDirections (hH : IsCircleModel T γ H)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading)
    (J : SmoothDirections U f) (K : SmoothDirections U g) :
    SmoothDirections U (fun x => circleProductBilinear hH hT hD hγ (f x) (g x)) :=
  (smoothDirectionsProd J K).compCircle hH
    (smoothTameOn_circleProduct hH hT hD hγ hi).choose (fun _ _ => mem_univ _)

def circleInverseComposeDirections (hH : IsCircleModel T γ H)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading) (travel : ℕ → ℝ)
    (J : SmoothDirections U f) (K : SmoothDirections U g)
    (hpos : MapsTo f U (circlePositiveLiftDomain H)) :
    SmoothDirections U
      (fun x => circlePositiveInverseComposeLinear hH hT hD hγ travel (f x) (g x)) :=
  (smoothDirectionsProd J K).compCircle hH
    (smoothTameOn_circlePositiveInverseComposeLinear hH hT hD hγ hi travel).choose
    (fun x hx => ⟨hpos hx, mem_univ _⟩)

def circleInversePerturbationDirections (hH : IsCircleModel T γ H)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading) (travel : ℕ → ℝ)
    (J : SmoothDirections U f) (hpos : MapsTo f U (circlePositiveLiftDomain H)) :
    SmoothDirections U
      (fun x => circlePositiveInversePerturbation hH hT hD hγ travel (f x)) :=
  J.compCircle hH
    (smoothTameOn_circlePositiveInversePerturbation hH hT hD hγ hi travel).choose hpos

def circleDerivativeDirections (hH : IsCircleModel T γ H) (J : SmoothDirections U f) :
    SmoothDirections U (fun x => circleDerivativeLinear hH (f x)) :=
  (solveSmoothDirectionsPostcomp J (circleDerivativeContinuousLinear hH)).congrOn
    (fun x _ => circleDerivativeContinuousLinear_apply hH (f x))

def circleSingletonDirections (hH : IsCircleModel T γ H) (m : ℕ)
    {a : E → ℝ} (J : SmoothDirections U a) :
    SmoothDirections U (fun x => circleSingletonLinear hH m (a x)) := by
  let L : ℝ →L[ℝ] H.Space :=
    ContinuousLinearMap.toSpanSingleton ℝ (circleSingletonLinear hH m 1)
  apply (solveSmoothDirectionsPostcomp J L).congrOn
  intro x hx
  change a x • circleSingletonLinear hH m 1 = circleSingletonLinear hH m (a x)
  simpa only [smul_eq_mul, mul_one] using
    ((circleSingletonLinear hH m).map_smul (a x) (1 : ℝ)).symm

end Operations

end ContinuousFlexibility.Statements
