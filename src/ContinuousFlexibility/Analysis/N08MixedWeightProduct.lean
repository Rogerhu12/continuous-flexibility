import ContinuousFlexibility.Analysis.N08WeightConjugation
import ContinuousFlexibility.Scalar.WeightedBinaryProduct
import ContinuousFlexibility.Scalar.WeightedProductTower
import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations
import ContinuousFlexibility.Scalar.WeightedWeightShift

/-!
# Actual multiplication with unequal physical weights

The normalization isometry reduces multiplication to weight zero. The result
has weight equal to the sum of the inputs, and agrees with every multiplication
realizing the physical decoder in `IsPhysicalSpaces`. This also gives a single
base and loss for its actual directional tower.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis SobolevModelData

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n08MixedWeightProduct (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (γ δ : ℝ) (u : (S.height γ).Space) (v : (S.height δ).Space) :
    (S.height (γ + δ)).Space :=
  n08WeightConjugation hT (hS.1 0) (hS.1 (γ + δ))
    (decodedProductMap hT (hS.1 0) ((hS.2.2.2.1 0).2.2) (le_refl 0) 1
      ![n08WeightConjugation hT (hS.1 γ) (hS.1 0) u,
        n08WeightConjugation hT (hS.1 δ) (hS.1 0) v])

private theorem n08_weight_product_cancel {a : ℝ} (ha : 0 < a)
    (γ δ u v : ℝ) :
    a ^ (γ + δ - 0) * ((a ^ (0 - γ) * u) * (a ^ (0 - δ) * v)) = u * v := by
  have hp : a ^ (γ + δ - 0) * (a ^ (0 - γ) * a ^ (0 - δ)) = 1 := by
    rw [← Real.rpow_add ha, ← Real.rpow_add ha]
    rw [show (γ + δ - 0) + (0 - γ + (0 - δ)) = 0 by ring, Real.rpow_zero]
  calc
    _ = (a ^ (γ + δ - 0) * (a ^ (0 - γ) * a ^ (0 - δ))) * (u * v) := by ring
    _ = u * v := by rw [hp, one_mul]

theorem n08MixedWeightProduct_decode (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (γ δ : ℝ)
    (u : (S.height γ).Space) (v : (S.height δ).Space) (p : PolarPoint) :
    (S.height (γ + δ)).decode (n08MixedWeightProduct hT hS γ δ u v) p =
      (S.height γ).decode u p * (S.height δ).decode v p := by
  by_cases hp : p ∈ annularOpen D
  · simp only [n08MixedWeightProduct, n08WeightConjugation_decode,
      n08WeightConjugationField_apply, decode_decodedProductMap_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact n08_weight_product_cancel ((hT.2.1 p.1 hp.1).2.1) γ δ _ _
  · rw [((hS.1 (γ + δ)).2.2.2.1
      (n08MixedWeightProduct hT hS γ δ u v)).2.2.2.1 p hp,
      ((hS.1 γ).2.2.2.1 u).2.2.2.1 p hp, zero_mul]

/-- Decoder injectivity identifies this construction with the multiplication
already supplied by the physical-space witness. -/
theorem n08MixedWeightProduct_eq_of_decode (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (γ δ : ℝ)
    (mul : (S.height γ).Space × (S.height δ).Space → (S.height (γ + δ)).Space)
    (hmul : ∀ u v p, (S.height (γ + δ)).decode (mul (u, v)) p =
      (S.height γ).decode u p * (S.height δ).decode v p)
    (u : (S.height γ).Space) (v : (S.height δ).Space) :
    n08MixedWeightProduct hT hS γ δ u v = mul (u, v) := by
  apply (hS.1 (γ + δ)).2.2.2.2.2.1
  funext p
  rw [n08MixedWeightProduct_decode, hmul]

theorem n08MixedWeightProduct_twoFactor (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (γ δ : ℝ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : (S.height γ).Space, ∀ v : (S.height δ).Space,
        (S.height (γ + δ)).grading s (n08MixedWeightProduct hT hS γ δ u v) ≤
          C * ((S.height γ).grading (s + loss) u * (S.height δ).grading base v +
            (S.height γ).grading base u * (S.height δ).grading (s + loss) v) := by
  obtain ⟨base, loss, hbase, hB⟩ := decodedProductMap_twoFactor
    hT (hS.1 0) ((hS.2.2.2.1 0).2.2) (le_refl 0)
  refine ⟨base, loss, hbase, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCu⟩ := hB s hs
  refine ⟨C, hC, fun u v => ?_⟩
  have h := hCu (n08WeightConjugation hT (hS.1 γ) (hS.1 0) u)
    (n08WeightConjugation hT (hS.1 δ) (hS.1 0) v)
  simpa only [n08MixedWeightProduct, n08WeightConjugation_grading, bilinearJetValue] using h

/-- A nonnegative-weight coefficient acts on a height without losing its
original weight. -/
def n08MixedWeightAction (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (u : (S.height γ).Space)
    (v : (S.height δ).Space) : (S.height δ).Space :=
  weightShift hT (hS.1 (γ + δ)) (hS.1 δ) (le_add_of_nonneg_left hγ)
    (n08MixedWeightProduct hT hS γ δ u v)

theorem n08MixedWeightAction_decode (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ)
    (u : (S.height γ).Space) (v : (S.height δ).Space) (p : PolarPoint) :
    (S.height δ).decode (n08MixedWeightAction hT hS hγ δ u v) p =
      (S.height γ).decode u p * (S.height δ).decode v p := by
  rw [n08MixedWeightAction, decode_weightShift, n08MixedWeightProduct_decode]

theorem n08MixedWeightAction_zero_right (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ)
    (u : (S.height γ).Space) : n08MixedWeightAction hT hS hγ δ u 0 = 0 := by
  apply (hS.1 δ).2.2.2.2.2.1
  funext p
  simp only [n08MixedWeightAction_decode, map_zero, Pi.zero_apply, mul_zero]

section Germ

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X} {γ δ : ℝ}
  {f : X → (S.height γ).Space} {g : X → (S.height δ).Space}

theorem UniformTameGerm.n08MixedWeightProduct
    (hf : UniformTameGerm p (S.height γ).grading x0 f)
    (hg : UniformTameGerm p (S.height δ).grading x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (S.height (γ + δ)).grading x0
      (fun x => n08MixedWeightProduct hT hS γ δ (f x) (g x)) := by
  letI : ∀ n, CompleteSpace ((S.height 0).level n) := fun n =>
    completeSpace_level_of_isSobolevModel (hS.1 0) n
  have hf0 := hf.postcompose hp ht (n08WeightConjugation hT (hS.1 γ) (hS.1 0))
    (n08WeightConjugation_isTame hT (hS.1 γ) (hS.1 0))
  have hg0 := hg.postcompose hp ht (n08WeightConjugation hT (hS.1 δ) (hS.1 0))
    (n08WeightConjugation_isTame hT (hS.1 δ) (hS.1 0))
  obtain ⟨base, loss, _, hB⟩ := decodedProductMap_twoFactor
    hT (hS.1 0) ((hS.2.2.2.1 0).2.2) (le_refl 0)
  have hprod := hf0.bilinear hg0
    (decodedProductMap hT (hS.1 0) ((hS.2.2.2.1 0).2.2) (le_refl 0) 1)
    hB hp ht (gradedSeminorm_monotone _ _) (withSeminorms_graded _ _)
  exact hprod.postcompose hp ht (n08WeightConjugation hT (hS.1 0) (hS.1 (γ + δ)))
    (n08WeightConjugation_isTame hT (hS.1 0) (hS.1 (γ + δ)))

theorem UniformTameGerm.n08MixedWeightAction
    (hf : UniformTameGerm p (S.height γ).grading x0 f)
    (hg : UniformTameGerm p (S.height δ).grading x0 g)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (S.height δ).grading x0
      (fun x => n08MixedWeightAction hT hS hγ δ (f x) (g x)) :=
  (hf.n08MixedWeightProduct hg hT hS hp ht).postcompose hp ht
    (weightShift hT (hS.1 (γ + δ)) (hS.1 δ) (le_add_of_nonneg_left hγ))
    (weightShift_isTame hT (hS.1 (γ + δ)) (hS.1 δ) (le_add_of_nonneg_left hγ))

end Germ

end ContinuousFlexibility.Statements
