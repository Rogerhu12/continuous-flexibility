import ContinuousFlexibility.Analysis.N07aMixedCoefficientTame
import ContinuousFlexibility.Analysis.N07aNormalizedSpaces
import ContinuousFlexibility.Analysis.N07aParameterGrading
import ContinuousFlexibility.Analysis.SolveTameSubspace
import ContinuousFlexibility.Analysis.SolveNewtonBridge

/-!
# Adding the actual scalar column on the normalized unknown space

The common-height forward map and the distinguished Source family are
combined by ordinary continuous linear maps. The grading is the induced
grading on the true normalization kernel.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)

def n07aNormalizedForwardCLM
    (F : (StateDirections S × ℝ) → HeightPair S →L[ℝ] S.Source)
    (N : (StateDirections S × ℝ) → S.Source) (z : StateDirections S × ℝ) :
    N07aNormalizedUnknown hD hT hS →L[ℝ] S.Source :=
  ((F z).comp (ContinuousLinearMap.fst ℝ (HeightPair S) ℝ) +
    (ContinuousLinearMap.snd ℝ (HeightPair S) ℝ).smulRight (N z)).comp
      (n07aNormalizationSubmodule hD hT hS).subtypeL

theorem n07aNormalizedForwardCLM_apply
    (F : (StateDirections S × ℝ) → HeightPair S →L[ℝ] S.Source)
    (N : (StateDirections S × ℝ) → S.Source) (z : StateDirections S × ℝ)
    (u : N07aNormalizedUnknown hD hT hS) :
    n07aNormalizedForwardCLM hD hT hS F N z u = F z u.val.1 + u.val.2 • N z := by
  simp only [n07aNormalizedForwardCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Submodule.subtypeL_apply]

theorem n07aNormalizedForwardCLM_smoothTame
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (F : (StateDirections S × ℝ) → HeightPair S →L[ℝ] S.Source)
    (N : (StateDirections S × ℝ) → S.Source)
    (hF : SmoothTameOn (n07aParameterHeightGrading S) S.sourceGrading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S => F z.1 z.2))
    (hN : SmoothTameOn (n07aParameterGrading S) S.sourceGrading U N) :
    SmoothTameOn (n07aParameterNormalizedGrading hD hT hS) S.sourceGrading
      (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS =>
        n07aNormalizedForwardCLM hD hT hS F N z.1 z.2) := by
  let Y := N07aNormalizedUnknown hD hT hS
  let p := n07aParameterGrading S
  let q := n07aNormalizedGrading hD hT hS
  let i : Y →L[ℝ] HeightPair S :=
    (ContinuousLinearMap.fst ℝ (HeightPair S) ℝ).comp
      (n07aNormalizationSubmodule hD hT hS).subtypeL
  let I : ((StateDirections S × ℝ) × Y) →L[ℝ] ((StateDirections S × ℝ) × HeightPair S) :=
    (ContinuousLinearMap.id ℝ (StateDirections S × ℝ)).prodMap i
  have hI (z : (StateDirections S × ℝ) × Y) : I z = (z.1, z.2.val.1) := by
    simp only [I, i, ContinuousLinearMap.coe_prodMap', Prod.map_apply',
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', Submodule.subtypeL_apply]
  have hi (n : ℕ) (z : (StateDirections S × ℝ) × Y) :
      n07aParameterHeightGrading S n (I z) ≤ 1 * pairGrading p q n z := by
    rw [hI]
    change p n z.1 + heightPairGrading S n z.2.val.1 ≤
      1 * (p n z.1 + (heightPairGrading S n z.2.val.1 + |z.2.val.2|))
    linarith only [abs_nonneg z.2.val.2]
  have hdom : I ⁻¹' (U ×ˢ univ) = U ×ˢ univ := by
    ext z
    simp only [mem_preimage, hI, mem_prod, mem_univ, and_true]
  have hFp := solve_smoothTameOn_precomp hF I (A := 1) le_rfl hi
  rw [hdom] at hFp
  have hFh := solve_smoothTameOn_postcomp (r := (S.height (3 / 4 : ℝ)).grading)
    hFp S.Q.toLinearMap.ker.subtypeL
    (B := 1) zero_le_one (fun n u => by
      simp only [Submodule.subtypeL_apply, one_mul, le_refl])
  have hNh := solve_smoothTameOn_postcomp (r := (S.height (3 / 4 : ℝ)).grading)
    hN S.Q.toLinearMap.ker.subtypeL
    (B := 1) zero_le_one (fun n u => by
      simp only [Submodule.subtypeL_apply, one_mul, le_refl])
  have hNf := n07a_height_smoothTame_fst hS
    (n07aParameterGrading_monotone S) (n07aParameterGrading_withSeminorms S)
    (n07aNormalizedGrading_monotone hD hT hS)
    (n07aNormalizedGrading_withSeminorms hD hT hS) hU hNh
  let m : ((StateDirections S × ℝ) × Y) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.snd ℝ (HeightPair S) ℝ).comp
      (n07aNormalizationSubmodule hD hT hS).subtypeL).comp
        (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) Y)
  have hm (z : (StateDirections S × ℝ) × Y) : m z = z.2.val.2 := by
    simp only [m, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', Submodule.subtypeL_apply]
  have hmt : IsTameLinear (pairGrading p q) realGrading m.toLinearMap 0 0 := by
    intro n _
    refine ⟨1, fun z => ?_⟩
    simp only [ContinuousLinearMap.coe_coe, hm]
    change |z.2.val.2| ≤ 1 *
      (p (n + 0) z.1 + (heightPairGrading S (n + 0) z.2.val.1 + |z.2.val.2|))
    simp only [Nat.add_zero, one_mul]
    linarith only [apply_nonneg (p n) z.1, apply_nonneg (heightPairGrading S n) z.2.val.1]
  have hmu := smoothTameOn_continuousLinear_on (hU.prod isOpen_univ) m hmt
  have hp := tamePairGrading_monotone (n07aParameterGrading_monotone S)
    (n07aNormalizedGrading_monotone hD hT hS)
  have ht := withSeminorms_pairGrading (n07aParameterGrading_withSeminorms S)
    (n07aNormalizedGrading_withSeminorms hD hT hS)
  letI : IsTopologicalAddGroup ((StateDirections S × ℝ) × Y) := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ ((StateDirections S × ℝ) × Y) := ht.continuousSMul
  have hproduct := n07a_height_smoothTame_smul_comp hS hp ht hmu hNf
  apply solve_smoothTameOn_codRestrict S.Q.toLinearMap.ker S.Q.isClosed_ker
    (smoothTameOn_add hp hFh hproduct)
  intro z _
  simp only [n07aNormalizedForwardCLM_apply, Submodule.coe_add, Submodule.coe_smul,
    hI, hm, Submodule.subtypeL_apply]

end ContinuousFlexibility.Analysis
