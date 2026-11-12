import ContinuousFlexibility.Analysis.N07aMixedCoefficientOperator
import ContinuousFlexibility.Scalar.WeightedHeightParameterPullback

/-!
# Smooth tame dependence of the actual mixed-weight divergence operator

Every term below is one of the established multiplication or fixed
differentiation maps. The conclusion concerns the prescribed operator,
with an unrestricted common-height argument.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n07a_height_smoothTame_fst
    {X Y : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {γ : ℝ} {f : X → (S.height γ).Space} {U : Set X}
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p)
    (hq : Monotone q) (hqt : WithSeminorms q) (hU : IsOpen U)
    (hf : SmoothTameOn p (S.height γ).grading U f) :
    SmoothTameOn (pairGrading p q) (S.height γ).grading (U ×ˢ univ)
      (fun z : X × Y => f z.1) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : LocallyConvexSpace ℝ X := ht.toLocallyConvexSpace
  letI : IsTopologicalAddGroup Y := hqt.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := hqt.continuousSMul
  letI : ∀ n, CompleteSpace ((S.height γ).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 γ) n
  have hfst := smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
    (ContinuousLinearMap.fst ℝ X Y) (scalar_pair_fst_isTame p q)
  exact smoothTameOn_comp_generic
    (f := fun z : X × Y => z.1) (g := f)
    (tamePairGrading_monotone hp hq) (withSeminorms_pairGrading ht hqt)
    ht hfst hf (fun _ hz => hz.1)

theorem n07a_smoothTame_scalarSMul
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] (q : ℕ → Seminorm ℝ F) :
    SmoothTameOn (pairGrading realGrading q) q univ
      (fun x : ℝ × F => x.1 • x.2) := by
  let P := pairGrading realGrading q
  have hB : ∀ s, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ × F,
      q s (bilinearJetValue (scalarSMulPairMultilinear (F := F)) x y) ≤
        C * (P (s + 0) x * P 0 y + P 0 x * P (s + 0) y) := by
    intro s _
    refine ⟨1, zero_le_one, fun x y => ?_⟩
    rw [scalarSMulPairMultilinear_apply, map_smul_eq_mul]
    simp only [Nat.add_zero, one_mul]
    have hx : ‖x.1‖ ≤ P 0 x := le_add_of_nonneg_right (apply_nonneg _ _)
    have hy : q s y.2 ≤ P s y := le_add_of_nonneg_left (norm_nonneg y.1)
    exact (mul_le_mul hx hy (apply_nonneg _ _) (apply_nonneg _ _)).trans
      (le_add_of_nonneg_left (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  apply smoothTameOn_congr (smoothTameOn_quadratic
    (scalarSMulPairMultilinear (F := F)) hB)
  intro x _
  exact scalarSMulPairMultilinear_apply x x

theorem n07a_height_smoothTame_smul_comp
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} {U : Set X} {γ : ℝ}
    {a : X → ℝ} {u : X → (S.height γ).Space}
    (hS : IsPhysicalSpaces D T S) (hp : Monotone p) (ht : WithSeminorms p)
    (ha : SmoothTameOn p realGrading U a)
    (hu : SmoothTameOn p (S.height γ).grading U u) :
    SmoothTameOn p (S.height γ).grading U (fun x => a x • u x) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : ∀ n, CompleteSpace ((S.height γ).level n) := fun n =>
    SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 γ) n
  let q := pairGrading realGrading (S.height γ).grading
  letI : LocallyConvexSpace ℝ (ℝ × (S.height γ).Space) :=
    (withSeminorms_pairGrading weighted_realGrading_withSeminorms
      (withSeminorms_graded _ _)).toLocallyConvexSpace
  have houter := n07a_smoothTame_scalarSMul (S.height γ).grading
  exact smoothTameOn_comp_generic hp ht
    (withSeminorms_pairGrading weighted_realGrading_withSeminorms
      (withSeminorms_graded _ _))
    (smoothTameOn_prodMk_generic hp ht ha hu) houter (fun _ _ => mem_univ _)

theorem n07aMixedCoefficientOperator_smoothTame_comp
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} {U : Set X}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 ≤ γ)
    {a b c : X → (S.height γ).Space} {u : X → ScalarCommonHeight S}
    (hp : Monotone p) (ht : WithSeminorms p)
    (ha : SmoothTameOn p (S.height γ).grading U a)
    (hb : SmoothTameOn p (S.height γ).grading U b)
    (hc : SmoothTameOn p (S.height γ).grading U c)
    (hu : SmoothTameOn p (scalarCommonHeightGrading S) U u) :
    SmoothTameOn p (S.height scalarBeta).grading U
      (fun x => n07aMixedCoefficientOperatorCLM hD hT hS hγ (a x) (b x) (c x) (u x)) := by
  have hpair : WithSeminorms (scalarCommonHeightGrading S) :=
    withSeminorms_pairGrading (withSeminorms_graded _ _) weighted_realGrading_withSeminorms
  have hur := n07a_height_smoothTame_postcompose hS hp ht hpair hu
    (scalarCommonRadialCLM hD hT hS) (scalarCommonRadialCLM_isTame hD hT hS)
  have hu₀ := n07a_height_smoothTame_postcompose hS hp ht hpair hu
    (scalarCommonProjectionCLM S) (scalarCommonProjectionCLM_isTame S)
  have hbθ := n07a_height_smoothTame_postcompose hS hp ht (withSeminorms_graded _ _) hb
    (SobolevModelData.angularSecondCLM hT (hS.1 γ))
    (SobolevModelData.angularSecondCLM_isTame hT (hS.1 γ))
  have huθ := n07a_height_smoothTame_postcompose hS hp ht (withSeminorms_graded _ _) hu₀
    (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta))
    (SobolevModelData.angularSecondCLM_isTame hT (hS.1 scalarBeta))
  have hn₁ := n07aMixedHeightMultiply_smoothTame_comp hT hS hγ hp ht ha hur
  have hn₂ := n07aMixedAngularJet_smoothTame_comp hT hS hγ hp ht hb hu₀
  have hn := smoothTameOn_add hp hn₁ hn₂
  have hdr := n07a_height_smoothTame_postcompose hS hp ht (withSeminorms_graded _ _) hn
    (SobolevModelData.radialCLM hT (hS.1 scalarBeta))
    (SobolevModelData.radialCLM_isTame hT (hS.1 scalarBeta))
  have hθ₁ := n07aMixedHeightMultiply_smoothTame_comp hT hS hγ hp ht hbθ hur
  have hθ₂ := n07aMixedAngularJet_smoothTame_comp hT hS hγ hp ht hb hur
  have hθ₃ := n07aMixedHeightMultiply_smoothTame_comp hT hS hγ hp ht hc huθ
  have hθ₄ := n07aMixedAngularJet_smoothTame_comp hT hS hγ hp ht hc hu₀
  exact smoothTameOn_add hp hdr
    (smoothTameOn_add hp (smoothTameOn_add hp (smoothTameOn_add hp hθ₁ hθ₂) hθ₃) hθ₄)

theorem n07aMixedCoefficientOperator_jointSmoothTame
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} {U : Set X}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 ≤ γ)
    {a b c : X → (S.height γ).Space}
    (hp : Monotone p) (ht : WithSeminorms p) (hU : IsOpen U)
    (ha : SmoothTameOn p (S.height γ).grading U a)
    (hb : SmoothTameOn p (S.height γ).grading U b)
    (hc : SmoothTameOn p (S.height γ).grading U c) :
    SmoothTameOn (pairGrading p (scalarCommonHeightGrading S)) (S.height scalarBeta).grading
      (U ×ˢ univ) (fun z : X × ScalarCommonHeight S =>
        n07aMixedCoefficientOperatorCLM hD hT hS hγ (a z.1) (b z.1) (c z.1) z.2) := by
  have hpc := weighted_scalarCommonHeightGrading_monotone S
  have htc := weighted_scalarCommonHeightGrading_withSeminorms S
  have ha' := n07a_height_smoothTame_fst hS hp ht hpc htc hU ha
  have hb' := n07a_height_smoothTame_fst hS hp ht hpc htc hU hb
  have hc' := n07a_height_smoothTame_fst hS hp ht hpc htc hU hc
  have hu := smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
    (ContinuousLinearMap.snd ℝ X (ScalarCommonHeight S))
    (scalar_pair_snd_isTame p (scalarCommonHeightGrading S))
  exact n07aMixedCoefficientOperator_smoothTame_comp hD hT hS hγ
    (tamePairGrading_monotone hp hpc) (withSeminorms_pairGrading ht htc) ha' hb' hc' hu

end ContinuousFlexibility.Analysis
