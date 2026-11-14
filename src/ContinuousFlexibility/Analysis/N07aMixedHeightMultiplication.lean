module

public import ContinuousFlexibility.Scalar.WeightedWeightShift
public import ContinuousFlexibility.Scalar.WeightedHeightSmooth

/-!
# Actual multiplication of a coefficient and a height

The physical-spaces certificate already supplies multiplication at the sum
of the input weights. Its genuine decoder makes it linear in the second
argument. The established weight inclusion then retains the unknown's
weight for every nonnegative coefficient weight. The same prescribed map
has a joint smooth tame tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n07aHeightProduct (hS : IsPhysicalSpaces D T S) (γ δ : ℝ) :
    (S.height γ).Space × (S.height δ).Space → (S.height (γ + δ)).Space :=
  (hS.2.2.2.2.2.1 γ δ).choose

theorem n07aHeightProduct_decode (hS : IsPhysicalSpaces D T S) (γ δ : ℝ)
    (a : (S.height γ).Space) (u : (S.height δ).Space) (p : PolarPoint) :
    (S.height (γ + δ)).decode (n07aHeightProduct hS γ δ (a, u)) p =
      (S.height γ).decode a p * (S.height δ).decode u p :=
  (hS.2.2.2.2.2.1 γ δ).choose_spec.1 a u p

theorem n07aHeightProduct_smoothTame (hS : IsPhysicalSpaces D T S) (γ δ : ℝ) :
    SmoothTameOn (pairGrading (S.height γ).grading (S.height δ).grading)
      (S.height (γ + δ)).grading univ (n07aHeightProduct hS γ δ) :=
  (hS.2.2.2.2.2.1 γ δ).choose_spec.2

theorem n07aHeightProduct_continuous (hS : IsPhysicalSpaces D T S) (γ δ : ℝ) :
    Continuous (n07aHeightProduct hS γ δ) :=
  continuousOn_univ.mp (n07aHeightProduct_smoothTame hS γ δ).choose.continuousOn

/-- Linearity is proved for the actual selected multiplication map by
its injective physical decoder. -/
def n07aHeightProductRightCLM (hS : IsPhysicalSpaces D T S) (γ δ : ℝ)
    (a : (S.height γ).Space) : (S.height δ).Space →L[ℝ] (S.height (γ + δ)).Space where
  toLinearMap :=
    { toFun := fun u => n07aHeightProduct hS γ δ (a, u)
      map_add' := by
        intro u v
        apply (hS.1 (γ + δ)).2.2.2.2.2.1
        funext p
        simp only [map_add, Pi.add_apply, n07aHeightProduct_decode]
        ring
      map_smul' := by
        intro c u
        apply (hS.1 (γ + δ)).2.2.2.2.2.1
        funext p
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          n07aHeightProduct_decode]
        ring }
  cont := (n07aHeightProduct_continuous hS γ δ).comp
    (continuous_const.prodMk continuous_id)

theorem n07aHeightProductRightCLM_apply (hS : IsPhysicalSpaces D T S) (γ δ : ℝ)
    (a : (S.height γ).Space) (u : (S.height δ).Space) :
    n07aHeightProductRightCLM hS γ δ a u = n07aHeightProduct hS γ δ (a, u) := rfl

/-- The coefficient weight is nonnegative; the height keeps its original
weight and the literal pointwise product. -/
def n07aMixedHeightMultiplyCLM (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (a : (S.height γ).Space) :
    (S.height δ).Space →L[ℝ] (S.height δ).Space :=
  (SobolevModelData.weightShift hT (hS.1 (γ + δ)) (hS.1 δ)
    (le_add_of_nonneg_left hγ)).comp (n07aHeightProductRightCLM hS γ δ a)

theorem n07aMixedHeightMultiplyCLM_apply
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (a : (S.height γ).Space) (u : (S.height δ).Space) :
    n07aMixedHeightMultiplyCLM hT hS hγ δ a u =
      SobolevModelData.weightShift hT (hS.1 (γ + δ)) (hS.1 δ)
        (le_add_of_nonneg_left hγ) (n07aHeightProduct hS γ δ (a, u)) := by
  simp only [n07aMixedHeightMultiplyCLM, ContinuousLinearMap.comp_apply,
    n07aHeightProductRightCLM_apply]

theorem n07aMixedHeightMultiplyCLM_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (a : (S.height γ).Space) (u : (S.height δ).Space)
    (p : PolarPoint) :
    (S.height δ).decode (n07aMixedHeightMultiplyCLM hT hS hγ δ a u) p =
      (S.height γ).decode a p * (S.height δ).decode u p := by
  rw [n07aMixedHeightMultiplyCLM_apply, SobolevModelData.decode_weightShift,
    n07aHeightProduct_decode]

theorem n07aMixedHeightMultiply_smoothTame
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) :
    SmoothTameOn (pairGrading (S.height γ).grading (S.height δ).grading)
      (S.height δ).grading univ
      (fun z : (S.height γ).Space × (S.height δ).Space =>
        n07aMixedHeightMultiplyCLM hT hS hγ δ z.1 z.2) := by
  letI : ∀ n, CompleteSpace ((S.height δ).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 δ) n
  exact smoothTameOn_postcompose_generic
    (tamePairGrading_monotone (gradedSeminorm_monotone _ _) (gradedSeminorm_monotone _ _))
    (withSeminorms_pairGrading (withSeminorms_graded _ _) (withSeminorms_graded _ _))
    (withSeminorms_graded _ _) (n07aHeightProduct_smoothTame hS γ δ)
    (SobolevModelData.weightShift hT (hS.1 (γ + δ)) (hS.1 δ)
      (le_add_of_nonneg_left hγ))
    (SobolevModelData.weightShift_isTame hT (hS.1 (γ + δ)) (hS.1 δ)
      (le_add_of_nonneg_left hγ))

theorem n07aMixedHeightMultiply_smoothTame_comp
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} {U : Set X}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ δ : ℝ} (hγ : 0 ≤ γ)
    {a : X → (S.height γ).Space} {u : X → (S.height δ).Space}
    (hp : Monotone p) (ht : WithSeminorms p)
    (ha : SmoothTameOn p (S.height γ).grading U a)
    (hu : SmoothTameOn p (S.height δ).grading U u) :
    SmoothTameOn p (S.height δ).grading U
      (fun x => n07aMixedHeightMultiplyCLM hT hS hγ δ (a x) (u x)) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : ∀ n, CompleteSpace ((S.height δ).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 δ) n
  exact smoothTameOn_comp_generic hp ht
    (withSeminorms_pairGrading (withSeminorms_graded _ _) (withSeminorms_graded _ _))
    (smoothTameOn_prodMk_generic hp ht ha hu)
    (n07aMixedHeightMultiply_smoothTame hT hS hγ δ) (fun _ _ => mem_univ _)

/-- Fixed tame differentiation maps can act on either of the two height
weights without changing the parameter domain. -/
theorem n07a_height_smoothTame_postcompose
    {X Y : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {U : Set X} {f : X → Y} {loss base : ℕ} {γ : ℝ}
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) (hqt : WithSeminorms q)
    (hf : SmoothTameOn p q U f)
    (L : Y →L[ℝ] (S.height γ).Space)
    (hL : IsTameLinear q (S.height γ).grading L.toLinearMap loss base) :
    SmoothTameOn p (S.height γ).grading U (fun x => L (f x)) := by
  letI : ∀ n, CompleteSpace ((S.height γ).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 γ) n
  exact smoothTameOn_postcompose_generic hp ht hqt hf L hL

end ContinuousFlexibility.Analysis
