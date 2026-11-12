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

private theorem n07aNormalizedForward_subtype_apply
    (u : N07aNormalizedUnknown hD hT hS) :
    (n07aNormalizationSubmodule hD hT hS).subtypeL u = u.val :=
  Submodule.subtypeL_apply (n07aNormalizationSubmodule hD hT hS) u

private theorem n07aNormalizedForward_grading_apply (n : ℕ)
    (u : N07aNormalizedUnknown hD hT hS) :
    n07aNormalizedGrading hD hT hS n u =
      heightPairGrading S n u.val.1 + |u.val.2| :=
  (n07aNormalizedGrading_apply hD hT hS n u).trans
    (pairGrading_apply (heightPairGrading S) realGrading n u.val)

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

private theorem n07aNormalizedForward_source_grading (n : ℕ) (u : S.Source) :
    (S.height (3 / 4 : ℝ)).grading n (S.Q.toLinearMap.ker.subtypeL u) =
      S.sourceGrading n u := by
  simp only [Submodule.subtypeL_apply, PhysicalSpacesData.sourceGrading,
    Seminorm.comp_apply, Submodule.subtype_apply]

private def n07aNormalizedForwardHeightProjectionCLM :
    ((StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS) →L[ℝ]
      ((StateDirections S × ℝ) × HeightPair S) :=
  (ContinuousLinearMap.id ℝ (StateDirections S × ℝ)).prodMap
    ((ContinuousLinearMap.fst ℝ (HeightPair S) ℝ).comp
      (n07aNormalizationSubmodule hD hT hS).subtypeL)

private theorem n07aNormalizedForwardHeightProjectionCLM_apply
    (z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS) :
    n07aNormalizedForwardHeightProjectionCLM hD hT hS z = (z.1, z.2.val.1) := by
  simp only [n07aNormalizedForwardHeightProjectionCLM,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']
  exact congrArg (fun u : HeightPair S × ℝ => (z.1, u.1))
    (n07aNormalizedForward_subtype_apply hD hT hS z.2)

private theorem n07aNormalizedForwardHeightProjectionCLM_bound (n : ℕ)
    (z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS) :
    n07aParameterHeightGrading S n (n07aNormalizedForwardHeightProjectionCLM hD hT hS z) ≤
      n07aParameterNormalizedGrading hD hT hS n z := by
  have he : n07aParameterHeightGrading S n
      (n07aNormalizedForwardHeightProjectionCLM hD hT hS z) =
      n07aParameterGrading S n z.1 + heightPairGrading S n z.2.val.1 :=
    (congrArg (fun v => n07aParameterHeightGrading S n v)
      (n07aNormalizedForwardHeightProjectionCLM_apply hD hT hS z)).trans
      (pairGrading_apply (n07aParameterGrading S) (heightPairGrading S)
        n (z.1, z.2.val.1))
  have hg : n07aParameterNormalizedGrading hD hT hS n z =
      n07aParameterGrading S n z.1 +
        (heightPairGrading S n z.2.val.1 + |z.2.val.2|) :=
    (pairGrading_apply (n07aParameterGrading S) (n07aNormalizedGrading hD hT hS) n z).trans
      (congrArg (fun t : ℝ => n07aParameterGrading S n z.1 + t)
        (n07aNormalizedForward_grading_apply hD hT hS n z.2))
  have hnum : n07aParameterGrading S n z.1 + heightPairGrading S n z.2.val.1 ≤
      n07aParameterGrading S n z.1 + (heightPairGrading S n z.2.val.1 + |z.2.val.2|) := by
    linarith only [abs_nonneg z.2.val.2]
  exact he.le.trans (hnum.trans_eq hg.symm)

private theorem n07aNormalizedForward_height_source_smoothTame
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (F : (StateDirections S × ℝ) → HeightPair S →L[ℝ] S.Source)
    (hF : SmoothTameOn (n07aParameterHeightGrading S) S.sourceGrading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S => F z.1 z.2)) :
    SmoothTameOn (n07aParameterNormalizedGrading hD hT hS) S.sourceGrading
      (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS =>
        F z.1 z.2.val.1) := by
  let I := n07aNormalizedForwardHeightProjectionCLM hD hT hS
  have hI (z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS) :
      I z = (z.1, z.2.val.1) :=
    n07aNormalizedForwardHeightProjectionCLM_apply hD hT hS z
  have hFp := solve_smoothTameOn_precomp (p := n07aParameterNormalizedGrading hD hT hS)
    hF I (A := 1) le_rfl
    (fun n z => by simpa only [one_mul] using
      n07aNormalizedForwardHeightProjectionCLM_bound hD hT hS n z)
  have hsub : U ×ˢ univ ⊆ I ⁻¹' (U ×ˢ univ) := by
    intro z hz
    have he : (I z).1 = z.1 :=
      congrArg (fun v : (StateDirections S × ℝ) × HeightPair S => v.1) (hI z)
    exact ⟨Eq.mpr (congrArg (fun v : StateDirections S × ℝ => v ∈ U) he) hz.1,
      mem_univ _⟩
  have hFp' := smoothTameOn_mono hFp (hU.prod isOpen_univ) hsub
  apply smoothTameOn_congr hFp'
  intro z _
  exact congrArg (fun v : (StateDirections S × ℝ) × HeightPair S => F v.1 v.2) (hI z)

private theorem n07aNormalizedForward_height_smoothTame
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (F : (StateDirections S × ℝ) → HeightPair S →L[ℝ] S.Source)
    (hF : SmoothTameOn (n07aParameterHeightGrading S) S.sourceGrading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S => F z.1 z.2)) :
    SmoothTameOn (n07aParameterNormalizedGrading hD hT hS)
      (S.height (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS =>
        (F z.1 z.2.val.1).val) := by
  have hFp := n07aNormalizedForward_height_source_smoothTame hD hT hS hU F hF
  have hFh := solve_smoothTameOn_postcomp (r := (S.height (3 / 4 : ℝ)).grading)
    hFp S.Q.toLinearMap.ker.subtypeL
    (B := 1) zero_le_one (fun n u => by
      simpa only [one_mul] using (n07aNormalizedForward_source_grading (S := S) n u).le)
  apply smoothTameOn_congr hFh
  intro z _
  exact Submodule.subtypeL_apply S.Q.toLinearMap.ker _

private theorem n07aNormalizedForward_scalar_smoothTame
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (N : (StateDirections S × ℝ) → S.Source)
    (hN : SmoothTameOn (n07aParameterGrading S) S.sourceGrading U N) :
    SmoothTameOn (n07aParameterNormalizedGrading hD hT hS)
      (S.height (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS =>
        z.2.val.2 • (N z.1).val) := by
  let Y := N07aNormalizedUnknown hD hT hS
  let p := n07aParameterGrading S
  let q := n07aNormalizedGrading hD hT hS
  have hgrading (n : ℕ) (z : (StateDirections S × ℝ) × Y) :
      pairGrading p q n z = p n z.1 +
        (heightPairGrading S n z.2.val.1 + |z.2.val.2|) :=
    (pairGrading_apply p q n z).trans (congrArg (fun t : ℝ => p n z.1 + t)
      (n07aNormalizedForward_grading_apply hD hT hS n z.2))
  have hNh := solve_smoothTameOn_postcomp (r := (S.height (3 / 4 : ℝ)).grading)
    hN S.Q.toLinearMap.ker.subtypeL
    (B := 1) zero_le_one (fun n u => by
      simpa only [one_mul] using (n07aNormalizedForward_source_grading (S := S) n u).le)
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
      ContinuousLinearMap.coe_snd']
    exact congrArg (fun u : HeightPair S × ℝ => u.2)
      (n07aNormalizedForward_subtype_apply hD hT hS z.2)
  have hmt : IsTameLinear (pairGrading p q) realGrading m.toLinearMap 0 0 := by
    intro n _
    refine ⟨1, fun z => ?_⟩
    have hnum : |z.2.val.2| ≤
        p n z.1 + (heightPairGrading S n z.2.val.1 + |z.2.val.2|) := by
      linarith only [apply_nonneg (p n) z.1,
        apply_nonneg (heightPairGrading S n) z.2.val.1]
    have hb : realGrading n (m.toLinearMap z) ≤ pairGrading p q n z :=
      (congrArg (fun t : ℝ => |t|) (hm z)).le.trans
        (hnum.trans_eq (hgrading n z).symm)
    simpa only [Nat.add_zero, NNReal.coe_one, one_mul] using hb
  have hmu := smoothTameOn_continuousLinear_on (hU.prod isOpen_univ) m hmt
  have hp := tamePairGrading_monotone (n07aParameterGrading_monotone S)
    (n07aNormalizedGrading_monotone hD hT hS)
  have ht := withSeminorms_pairGrading (n07aParameterGrading_withSeminorms S)
    (n07aNormalizedGrading_withSeminorms hD hT hS)
  letI : IsTopologicalAddGroup ((StateDirections S × ℝ) × Y) := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ ((StateDirections S × ℝ) × Y) := ht.continuousSMul
  have hproduct := n07a_height_smoothTame_smul_comp hS hp ht hmu hNf
  apply smoothTameOn_congr hproduct
  intro z _
  simp only [hm, Submodule.subtypeL_apply]

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
  have hheight := n07aNormalizedForward_height_smoothTame hD hT hS hU F hF
  have hscalar := n07aNormalizedForward_scalar_smoothTame hD hT hS hU N hN
  have hp : Monotone (n07aParameterNormalizedGrading hD hT hS) :=
    tamePairGrading_monotone (n07aParameterGrading_monotone S)
      (n07aNormalizedGrading_monotone hD hT hS)
  have ht : WithSeminorms (n07aParameterNormalizedGrading hD hT hS) :=
    withSeminorms_pairGrading (n07aParameterGrading_withSeminorms S)
      (n07aNormalizedGrading_withSeminorms hD hT hS)
  letI : IsTopologicalAddGroup ((StateDirections S × ℝ) ×
      N07aNormalizedUnknown hD hT hS) := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ ((StateDirections S × ℝ) ×
      N07aNormalizedUnknown hD hT hS) := ht.continuousSMul
  apply solve_smoothTameOn_codRestrict S.Q.toLinearMap.ker S.Q.isClosed_ker
    (smoothTameOn_add hp hheight hscalar)
  intro z _
  simp only [n07aNormalizedForwardCLM_apply, Submodule.coe_add, Submodule.coe_smul]

end ContinuousFlexibility.Analysis
