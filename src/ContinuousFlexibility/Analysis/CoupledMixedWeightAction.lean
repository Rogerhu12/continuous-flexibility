module

public import ContinuousFlexibility.Scalar.WeightedWeightShift
public import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear

/-!
# A weak positive coefficient acts on the original strong height space

The physical multiplication theorem adds the two weights. The canonical
weight inclusion then returns to the weight of the second argument. This
preserves the actual product, both independent linearities, and the genuine
joint smooth tame tower on the full product domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The actual mixed-weight multiplication already supplied by W02. -/
def coupledWeightProduct (hS : IsPhysicalSpaces D T S) (γ δ : ℝ) :
    (S.height γ).Space × (S.height δ).Space → (S.height (γ + δ)).Space :=
  Classical.choose (hS.2.2.2.2.2.1 γ δ)

theorem coupledWeightProduct_decode (hS : IsPhysicalSpaces D T S) (γ δ : ℝ)
    (u : (S.height γ).Space) (v : (S.height δ).Space) (p : PolarPoint) :
    (S.height (γ + δ)).decode (coupledWeightProduct hS γ δ (u, v)) p =
      (S.height γ).decode u p * (S.height δ).decode v p :=
  (Classical.choose_spec (hS.2.2.2.2.2.1 γ δ)).1 u v p

theorem coupledWeightProduct_smoothTameOn (hS : IsPhysicalSpaces D T S) (γ δ : ℝ) :
    SmoothTameOn (pairGrading (S.height γ).grading (S.height δ).grading)
      (S.height (γ + δ)).grading univ (coupledWeightProduct hS γ δ) :=
  (Classical.choose_spec (hS.2.2.2.2.2.1 γ δ)).2

/-- Multiplication by a nonnegative-weight field, retaining the original
weight of the independent second field. -/
def coupledMixedWeightAction (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ)
    (u : (S.height γ).Space) (v : (S.height δ).Space) : (S.height δ).Space :=
  SobolevModelData.weightShift hT (hS.1 (γ + δ)) (hS.1 δ)
    (le_add_of_nonneg_left hγ) (coupledWeightProduct hS γ δ (u, v))

theorem coupledMixedWeightAction_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ)
    (u : (S.height γ).Space) (v : (S.height δ).Space) (p : PolarPoint) :
    (S.height δ).decode (coupledMixedWeightAction hT hS hγ δ u v) p =
      (S.height γ).decode u p * (S.height δ).decode v p :=
  (congrFun (SobolevModelData.decode_weightShift hT (hS.1 (γ + δ)) (hS.1 δ)
    (le_add_of_nonneg_left hγ) (coupledWeightProduct hS γ δ (u, v))) p).trans
      (coupledWeightProduct_decode hS γ δ u v p)

theorem coupledMixedWeightAction_add_right
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (u : (S.height γ).Space)
    (v w : (S.height δ).Space) :
    coupledMixedWeightAction hT hS hγ δ u (v + w) =
      coupledMixedWeightAction hT hS hγ δ u v + coupledMixedWeightAction hT hS hγ δ u w := by
  apply (hS.1 δ).2.2.2.2.2.1
  funext p
  simp only [coupledMixedWeightAction_decode, map_add, Pi.add_apply]
  ring

theorem coupledMixedWeightAction_smul_right
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (u : (S.height γ).Space)
    (c : ℝ) (v : (S.height δ).Space) :
    coupledMixedWeightAction hT hS hγ δ u (c • v) =
      c • coupledMixedWeightAction hT hS hγ δ u v := by
  apply (hS.1 δ).2.2.2.2.2.1
  funext p
  simp only [coupledMixedWeightAction_decode, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem coupledMixedWeightAction_add_left
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (u v : (S.height γ).Space)
    (w : (S.height δ).Space) :
    coupledMixedWeightAction hT hS hγ δ (u + v) w =
      coupledMixedWeightAction hT hS hγ δ u w + coupledMixedWeightAction hT hS hγ δ v w := by
  apply (hS.1 δ).2.2.2.2.2.1
  funext p
  simp only [coupledMixedWeightAction_decode, map_add, Pi.add_apply]
  ring

theorem coupledMixedWeightAction_smul_left
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (c : ℝ) (u : (S.height γ).Space)
    (v : (S.height δ).Space) :
    coupledMixedWeightAction hT hS hγ δ (c • u) v =
      c • coupledMixedWeightAction hT hS hγ δ u v := by
  apply (hS.1 δ).2.2.2.2.2.1
  funext p
  simp only [coupledMixedWeightAction_decode, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

def coupledMixedWeightActionLinear
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) :
    (S.height γ).Space →ₗ[ℝ] (S.height δ).Space →ₗ[ℝ] (S.height δ).Space where
  toFun u :=
    { toFun := coupledMixedWeightAction hT hS hγ δ u
      map_add' := coupledMixedWeightAction_add_right hT hS hγ δ u
      map_smul' := coupledMixedWeightAction_smul_right hT hS hγ δ u }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    exact coupledMixedWeightAction_add_left hT hS hγ δ u v w
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    exact coupledMixedWeightAction_smul_left hT hS hγ δ c u v

theorem coupledMixedWeightActionLinear_apply
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ)
    (u : (S.height γ).Space) (v : (S.height δ).Space) :
    coupledMixedWeightActionLinear hT hS hγ δ u v =
      coupledMixedWeightAction hT hS hγ δ u v := rfl

theorem coupledMixedWeightAction_continuous
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) :
    Continuous (fun z : (S.height γ).Space × (S.height δ).Space =>
      coupledMixedWeightAction hT hS hγ δ z.1 z.2) := by
  obtain ⟨J, _⟩ := coupledWeightProduct_smoothTameOn hS γ δ
  exact (SobolevModelData.weightShift hT (hS.1 (γ + δ)) (hS.1 δ)
    (le_add_of_nonneg_left hγ)).continuous.comp (continuousOn_univ.mp J.continuousOn)

/-- The independent source variable has an actual continuous linear map
for every fixed weak coefficient. -/
def coupledMixedWeightActionCLM
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (u : (S.height γ).Space) :
    (S.height δ).Space →L[ℝ] (S.height δ).Space where
  toLinearMap := coupledMixedWeightActionLinear hT hS hγ δ u
  cont := (coupledMixedWeightAction_continuous hT hS hγ δ).comp
    (continuous_const.prodMk continuous_id)

theorem coupledMixedWeightActionCLM_apply
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ)
    (u : (S.height γ).Space) (v : (S.height δ).Space) :
    coupledMixedWeightActionCLM hT hS hγ δ u v =
      coupledMixedWeightAction hT hS hγ δ u v := rfl

theorem coupledMixedWeightAction_smoothTameOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) :
    SmoothTameOn (pairGrading (S.height γ).grading (S.height δ).grading)
      (S.height δ).grading univ
      (fun z => coupledMixedWeightAction hT hS hγ δ z.1 z.2) := by
  letI : ∀ n, CompleteSpace ((S.height δ).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 δ) n
  exact smoothTameOn_postcompose_generic
    (tamePairGrading_monotone (gradedSeminorm_monotone _ _) (gradedSeminorm_monotone _ _))
    (withSeminorms_pairGrading (withSeminorms_graded _ _) (withSeminorms_graded _ _))
    (withSeminorms_graded _ _) (coupledWeightProduct_smoothTameOn hS γ δ)
    (SobolevModelData.weightShift hT (hS.1 (γ + δ)) (hS.1 δ) (le_add_of_nonneg_left hγ))
    (SobolevModelData.weightShift_isTame hT (hS.1 (γ + δ)) (hS.1 δ)
      (le_add_of_nonneg_left hγ))

section Composition

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {U : Set X} {γ δ : ℝ}
  {f : X → (S.height γ).Space} {g : X → (S.height δ).Space}

theorem SmoothTameOn.coupledMixedWeightAction
    (hf : SmoothTameOn p (S.height γ).grading U f)
    (hg : SmoothTameOn p (S.height δ).grading U g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    SmoothTameOn p (S.height δ).grading U
      (fun x => coupledMixedWeightAction hT hS hγ δ (f x) (g x)) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : ∀ n, CompleteSpace ((S.height δ).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 δ) n
  have hpair := smoothTameOn_prodMk_generic hp ht hf hg
  have htop : WithSeminorms (pairGrading (S.height γ).grading (S.height δ).grading) :=
    withSeminorms_pairGrading (withSeminorms_graded _ _) (withSeminorms_graded _ _)
  letI : LocallyConvexSpace ℝ ((S.height γ).Space × (S.height δ).Space) :=
    htop.toLocallyConvexSpace
  have hcomp := smoothTameOn_comp_generic hp ht htop hpair
    (coupledMixedWeightAction_smoothTameOn hT hS hγ δ) (fun _ _ => mem_univ _)
  simpa only [Function.comp_def] using hcomp

end Composition

end ContinuousFlexibility.Statements
