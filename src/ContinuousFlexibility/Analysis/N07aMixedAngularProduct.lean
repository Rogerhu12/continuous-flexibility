import ContinuousFlexibility.Analysis.N07aMixedHeightMultiplication
import ContinuousFlexibility.Scalar.WeightedAngularJetProduct

/-!
# Products of odd angular jets at different height weights

Polarizing the second angular derivative of the actual mixed-weight
product gives the product of the two first angular derivatives. This
uses only the original even height spaces and retains the unknown's
weight, with a continuous linear map at each fixed coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n07aMixedAngularJetCLM
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ) (a : (S.height γ).Space) :
    (S.height δ).Space →L[ℝ] (S.height δ).Space :=
  (1 / 2 : ℝ) •
    ((SobolevModelData.angularSecondCLM hT (hS.1 δ)).comp
        (n07aMixedHeightMultiplyCLM hT hS hγ δ a) -
      n07aMixedHeightMultiplyCLM hT hS hγ δ
        (SobolevModelData.angularSecondCLM hT (hS.1 γ) a) -
      (n07aMixedHeightMultiplyCLM hT hS hγ δ a).comp
        (SobolevModelData.angularSecondCLM hT (hS.1 δ)))

theorem n07aMixedAngularJetCLM_apply
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 ≤ γ) (δ : ℝ)
    (a : (S.height γ).Space) (u : (S.height δ).Space) :
    n07aMixedAngularJetCLM hT hS hγ δ a u =
      (1 / 2 : ℝ) •
        (SobolevModelData.angularSecondCLM hT (hS.1 δ)
            (n07aMixedHeightMultiplyCLM hT hS hγ δ a u) -
          n07aMixedHeightMultiplyCLM hT hS hγ δ
            (SobolevModelData.angularSecondCLM hT (hS.1 γ) a) u -
          n07aMixedHeightMultiplyCLM hT hS hγ δ a
            (SobolevModelData.angularSecondCLM hT (hS.1 δ) u)) := by
  simp only [n07aMixedAngularJetCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]

theorem n07aMixedAngularJetCLM_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (a : (S.height γ).Space) (u : (S.height δ).Space) (p : PolarPoint) :
    (S.height δ).decode (n07aMixedAngularJetCLM hT hS hγ.le δ a u) p =
      angularPartial ((S.height γ).decode a) p * angularPartial ((S.height δ).decode u) p := by
  have ha := (heightMember_contDiff_and_flatJets hT hγ ((hS.1 γ).2.2.2.1 a)).1
  have hu := (heightMember_contDiff_and_flatJets hT hδ ((hS.1 δ).2.2.2.1 u)).1
  have hM : (S.height δ).decode (n07aMixedHeightMultiplyCLM hT hS hγ.le δ a u) =
      fun q => (S.height γ).decode a q * (S.height δ).decode u q :=
    funext (n07aMixedHeightMultiplyCLM_decode hT hS hγ.le δ a u)
  rw [n07aMixedAngularJetCLM_apply]
  simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    SobolevModelData.decode_angularSecondCLM, hM,
    n07aMixedHeightMultiplyCLM_decode]
  rw [angularPartial_product_twice ha hu]
  ring

theorem n07aMixedAngularJet_smoothTame_comp
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} {U : Set X}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ δ : ℝ} (hγ : 0 ≤ γ)
    {a : X → (S.height γ).Space} {u : X → (S.height δ).Space}
    (hp : Monotone p) (ht : WithSeminorms p)
    (ha : SmoothTameOn p (S.height γ).grading U a)
    (hu : SmoothTameOn p (S.height δ).grading U u) :
    SmoothTameOn p (S.height δ).grading U
      (fun x => n07aMixedAngularJetCLM hT hS hγ δ (a x) (u x)) := by
  have ha' := n07a_height_smoothTame_postcompose hS hp ht (withSeminorms_graded _ _) ha
    (SobolevModelData.angularSecondCLM hT (hS.1 γ))
    (SobolevModelData.angularSecondCLM_isTame hT (hS.1 γ))
  have hu' := n07a_height_smoothTame_postcompose hS hp ht (withSeminorms_graded _ _) hu
    (SobolevModelData.angularSecondCLM hT (hS.1 δ))
    (SobolevModelData.angularSecondCLM_isTame hT (hS.1 δ))
  have hm := n07aMixedHeightMultiply_smoothTame_comp hT hS hγ hp ht ha hu
  have hfirst := n07a_height_smoothTame_postcompose hS hp ht (withSeminorms_graded _ _) hm
    (SobolevModelData.angularSecondCLM hT (hS.1 δ))
    (SobolevModelData.angularSecondCLM_isTame hT (hS.1 δ))
  have hsecond := n07aMixedHeightMultiply_smoothTame_comp hT hS hγ hp ht ha' hu
  have hthird := n07aMixedHeightMultiply_smoothTame_comp hT hS hγ hp ht ha hu'
  have hn₂ := n07a_height_smoothTame_postcompose hS hp ht (withSeminorms_graded _ _) hsecond
    (-ContinuousLinearMap.id ℝ (S.height δ).Space) (IsTameLinear.id (S.height δ).grading).neg
  have hn₃ := n07a_height_smoothTame_postcompose hS hp ht (withSeminorms_graded _ _) hthird
    (-ContinuousLinearMap.id ℝ (S.height δ).Space) (IsTameLinear.id (S.height δ).grading).neg
  have hs := smoothTameOn_add hp (smoothTameOn_add hp hfirst hn₂) hn₃
  have hhalf := n07a_height_smoothTame_postcompose hS hp ht (withSeminorms_graded _ _) hs
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (S.height δ).Space)
    ((IsTameLinear.id (S.height δ).grading).smul (1 / 2))
  apply smoothTameOn_congr hhalf
  intro x _
  simp only [n07aMixedAngularJetCLM_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg]

end ContinuousFlexibility.Analysis
