module

public import ContinuousFlexibility.Analysis.CoupledQuadraticAlgebra
public import ContinuousFlexibility.Analysis.CoupledWeakScalarErrorSmooth
public import ContinuousFlexibility.Analysis.CoupledScalarActionSmooth
public import ContinuousFlexibility.Analysis.SolveResidualSpaces

/-!
# Joint smooth tameness of the independent coupled error

The coefficient, recovered height, and recovered circle solution are used
on their common parameter neighborhood. Both residual arguments remain
unrestricted. The constructed source and even-circle components retain
their original codomains throughout the composition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Projections

variable {E F Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

private theorem coupled_error_fst_smoothTameOn
    {p : ℕ → Seminorm ℝ Z} {q : ℕ → Seminorm ℝ E} {r : ℕ → Seminorm ℝ F}
    {U : Set Z} {f : Z → E × F} (hf : SmoothTameOn p (pairGrading q r) U f) :
    SmoothTameOn p q U (fun z => (f z).1) := by
  exact solve_smoothTameOn_postcomp hf (ContinuousLinearMap.fst ℝ E F)
    (B := 1) zero_le_one (fun n z => by
      change q n z.1 ≤ 1 * (q n z.1 + r n z.2)
      simpa only [one_mul] using le_add_of_nonneg_right (apply_nonneg (r n) z.2))

private theorem coupled_error_snd_smoothTameOn
    {p : ℕ → Seminorm ℝ Z} {q : ℕ → Seminorm ℝ E} {r : ℕ → Seminorm ℝ F}
    {U : Set Z} {f : Z → E × F} (hf : SmoothTameOn p (pairGrading q r) U f) :
    SmoothTameOn p r U (fun z => (f z).2) := by
  exact solve_smoothTameOn_postcomp hf (ContinuousLinearMap.snd ℝ E F)
    (B := 1) zero_le_one (fun n z => by
      change r n z.2 ≤ 1 * (q n z.1 + r n z.2)
      simpa only [one_mul] using le_add_of_nonneg_left (apply_nonneg (q n) z.1))

private theorem coupled_error_subtype_smoothTameOn
    {p : ℕ → Seminorm ℝ Z} {q : ℕ → Seminorm ℝ E}
    (W : Submodule ℝ E) {U : Set Z} {f : Z → W}
    (hf : SmoothTameOn p (fun n => (q n).comp W.subtype) U f) :
    SmoothTameOn p q U (fun z => (f z).val) := by
  exact solve_smoothTameOn_postcomp hf W.subtypeL (B := 1) zero_le_one (fun n z => by
    change q n z.val ≤ 1 * q n z.val
    exact le_of_eq (one_mul _).symm)

private theorem coupled_error_ignore_right
    {p : ℕ → Seminorm ℝ E} (q : ℕ → Seminorm ℝ F) {r : ℕ → Seminorm ℝ Z}
    {U : Set E} {f : E → Z} (hf : SmoothTameOn p r U f) :
    SmoothTameOn (pairGrading p q) r (U ×ˢ univ) (fun z : E × F => f z.1) := by
  let L := ContinuousLinearMap.fst ℝ E F
  have hb : ∀ n z, p n (L z) ≤ 1 * pairGrading p q n z := by
    intro n z
    change p n z.1 ≤ 1 * (p n z.1 + q n z.2)
    simpa only [one_mul] using le_add_of_nonneg_right (apply_nonneg (q n) z.2)
  have h := solve_smoothTameOn_precomp hf L (A := 1) le_rfl hb
  have hd : L ⁻¹' U = U ×ˢ univ := by
    ext z
    simp only [mem_preimage, L, ContinuousLinearMap.coe_fst', mem_prod, mem_univ, and_true]
  rw [hd] at h
  exact h

private theorem coupled_error_forget_middle
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ Z}
    {U : Set E} {f : E × F → Z} (hf : SmoothTameOn (pairGrading p q) r (U ×ˢ univ) f) :
    SmoothTameOn (pairGrading (pairGrading p q) q) r ((U ×ˢ univ) ×ˢ univ)
      (fun z : (E × F) × F => f (z.1.1, z.2)) := by
  let L : ((E × F) × F) →L[ℝ] E × F :=
    ((ContinuousLinearMap.fst ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) F)).prod
      (ContinuousLinearMap.snd ℝ (E × F) F)
  have hL (z : (E × F) × F) : L z = (z.1.1, z.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hb : ∀ n z, pairGrading p q n (L z) ≤
      1 * pairGrading (pairGrading p q) q n z := by
    intro n z
    rw [hL, one_mul]
    change p n z.1.1 + q n z.2 ≤ (p n z.1.1 + q n z.1.2) + q n z.2
    exact add_le_add (le_add_of_nonneg_right (apply_nonneg (q n) z.1.2)) le_rfl
  have h := solve_smoothTameOn_precomp hf L (A := 1) le_rfl hb
  have hd : L ⁻¹' (U ×ˢ univ) = (U ×ˢ univ) ×ˢ univ := by
    ext z
    simp only [mem_preimage, hL, mem_prod, mem_univ, and_true]
  rw [hd] at h
  exact smoothTameOn_congr h (fun z _ => congrArg f (hL z))

private theorem coupled_error_product_projections
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} (hU : IsOpen U) :
    SmoothTameOn (pairGrading (pairGrading p q) q) p ((U ×ˢ univ) ×ˢ univ)
        (fun z : (E × F) × F => z.1.1) ∧
      SmoothTameOn (pairGrading (pairGrading p q) q) q ((U ×ˢ univ) ×ˢ univ)
        (fun z : (E × F) × F => z.1.2) := by
  have hfirst : SmoothTameOn (pairGrading (pairGrading p q) q) (pairGrading p q)
      ((U ×ˢ univ) ×ˢ univ) (fun z : (E × F) × F => z.1) :=
    smoothTameOn_continuousLinear_on ((hU.prod isOpen_univ).prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ (E × F) F) (scalar_pair_fst_isTame (pairGrading p q) q)
  exact ⟨coupled_error_fst_smoothTameOn hfirst, coupled_error_snd_smoothTameOn hfirst⟩

end Projections

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

private abbrev coupledErrorParameterGrading (S : PhysicalSpacesData) :=
  pairGrading (sectorGrading S) realGrading

private abbrev coupledErrorSingleInputGrading (S : PhysicalSpacesData) :=
  pairGrading (coupledErrorParameterGrading S) (residualGrading S)

private abbrev coupledErrorFullInputGrading (S : PhysicalSpacesData) :=
  pairGrading (coupledErrorSingleInputGrading S) (residualGrading S)

private abbrev coupledErrorCircleParameterGrading (S : PhysicalSpacesData) :=
  pairGrading (coupledErrorParameterGrading S) (S.circle (3 / 4 : ℝ)).grading

private abbrev coupledErrorHeightActionGrading (S : PhysicalSpacesData) :=
  pairGrading (coupledErrorCircleParameterGrading S) (heightPairGrading S)

private abbrev coupledErrorCircleActionGrading (S : PhysicalSpacesData) :=
  pairGrading (coupledErrorCircleParameterGrading S) (S.circle (3 / 4 : ℝ)).grading

private theorem coupled_error_grading_facts (S : PhysicalSpacesData) :
    Monotone (coupledErrorFullInputGrading S) ∧
      WithSeminorms (coupledErrorFullInputGrading S) ∧
      WithSeminorms (coupledErrorParameterGrading S) := by
  have hp : Monotone (coupledErrorParameterGrading S) := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms (coupledErrorParameterGrading S) := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have hr : Monotone (residualGrading S) := tamePairGrading_monotone
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)
  have htr : WithSeminorms (residualGrading S) := withSeminorms_pairGrading
    (coupled_sourceGrading_withSeminorms S)
    ((Topology.IsInducing.subtypeVal).withSeminorms
      (f := (evenCircleSubmodule S).subtype) (withSeminorms_graded _ _))
  exact ⟨tamePairGrading_monotone (tamePairGrading_monotone hp hr) hr,
    withSeminorms_pairGrading (withSeminorms_pairGrading htp htr) htr, htp⟩

private theorem coupled_error_scale_smoothTameOn
    (S : PhysicalSpacesData) {U : Set (StateDirections S × ℝ)} (hU : IsOpen U) :
    SmoothTameOn (coupledErrorParameterGrading S) realGrading U
      (fun z : StateDirections S × ℝ => z.2) :=
  smoothTameOn_continuousLinear_on hU (ContinuousLinearMap.snd ℝ (StateDirections S) ℝ)
    (scalar_pair_snd_isTame (sectorGrading S) realGrading)

section GenericAssembly

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {U : Set X} {W : Set Y} {parameter : X → Y}

private theorem coupled_error_source_assemble
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    {a : X → ℝ} {t : X → CoupledWeakHeight S} {source : X → ScalarHeightSpace S}
    {height : X → HeightPair S} {circle : X → CircleSpace S}
    {error : (Y × CircleSpace S) × HeightPair S → S.Source}
    (hparameter : SmoothTameOn p q U parameter)
    (ha : SmoothTameOn p realGrading U a)
    (ht : SmoothTameOn p (coupledWeakHeightGrading S) U t)
    (hs : SmoothTameOn p (scalarHeightGrading S) U source)
    (hh : SmoothTameOn p (heightPairGrading S) U height)
    (hc : SmoothTameOn p (S.circle (3 / 4 : ℝ)).grading U circle)
    (he : SmoothTameOn
      (pairGrading (pairGrading q (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
      S.sourceGrading ((W ×ˢ univ) ×ˢ univ) error)
    (hmap : MapsTo parameter U W) :
    SmoothTameOn p S.sourceGrading U
      (fun x => a x • coupledScalarTypeErrorSourceLinear hD hT hS (t x) (source x) (height x) +
        error ((parameter x, circle x), height x)) := by
  letI : IsTopologicalAddGroup X := htp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := htp.continuousSMul
  letI : IsTopologicalAddGroup Y := htq.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := htq.continuousSMul
  have htc : WithSeminorms (S.circle (3 / 4 : ℝ)).grading := withSeminorms_graded _ _
  have hth := coupled_heightPairGrading_withSeminorms S
  have hts := coupled_sourceGrading_withSeminorms S
  letI : IsTopologicalAddGroup (CircleSpace S) := htc.isTopologicalAddGroup
  letI : ContinuousSMul ℝ (CircleSpace S) := htc.continuousSMul
  letI : IsTopologicalAddGroup (HeightPair S) := hth.isTopologicalAddGroup
  letI : ContinuousSMul ℝ (HeightPair S) := hth.continuousSMul
  letI : IsTopologicalAddGroup S.Source := hts.isTopologicalAddGroup
  letI : ContinuousSMul ℝ S.Source := hts.continuousSMul
  have hscalar := coupled_smoothTameOn_source_smul hS hp htp ha
    (coupledWeakTypeErrorSourceLinear_smoothTameOn hD hT hS hp htp ht hs hh)
  have htL := withSeminorms_pairGrading (withSeminorms_pairGrading htq htc) hth
  letI : IsTopologicalAddGroup ((Y × CircleSpace S) × HeightPair S) :=
    htL.isTopologicalAddGroup
  letI : ContinuousSMul ℝ ((Y × CircleSpace S) × HeightPair S) := htL.continuousSMul
  letI : LocallyConvexSpace ℝ ((Y × CircleSpace S) × HeightPair S) := htL.toLocallyConvexSpace
  have herror := coupled_smoothTameOn_comp_source hS hp htp htL
    (smoothTameOn_prodMk_generic hp htp
      (smoothTameOn_prodMk_generic hp htp hparameter hc) hh) he
    (fun x hx => ⟨⟨hmap hx, mem_univ _⟩, mem_univ _⟩)
  exact smoothTameOn_add hp hscalar herror

private theorem coupled_error_even_assemble
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    {circle inverse : X → CircleSpace S}
    {error : (Y × CircleSpace S) × CircleSpace S → CircleSpace S}
    (hparameter : SmoothTameOn p q U parameter)
    (hc : SmoothTameOn p (S.circle (3 / 4 : ℝ)).grading U circle)
    (hi : SmoothTameOn p (S.circle (3 / 4 : ℝ)).grading U inverse)
    (he : SmoothTameOn
      (pairGrading (pairGrading q (S.circle (3 / 4 : ℝ)).grading)
        (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading ((W ×ˢ univ) ×ˢ univ) error)
    (hmap : MapsTo parameter U W) :
    SmoothTameOn p (evenCircleGradingAt S (3 / 4 : ℝ)) U
      (fun x => coupledEvenProjectionCLM hS (error ((parameter x, circle x), inverse x))) := by
  letI : IsTopologicalAddGroup X := htp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := htp.continuousSMul
  letI : IsTopologicalAddGroup Y := htq.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := htq.continuousSMul
  have htc : WithSeminorms (S.circle (3 / 4 : ℝ)).grading := withSeminorms_graded _ _
  letI : IsTopologicalAddGroup (CircleSpace S) := htc.isTopologicalAddGroup
  letI : ContinuousSMul ℝ (CircleSpace S) := htc.continuousSMul
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.2.1 (3 / 4 : ℝ)).2.1 n).isComplete.completeSpace_coe
  have htR := withSeminorms_pairGrading (withSeminorms_pairGrading htq htc) htc
  letI : IsTopologicalAddGroup ((Y × CircleSpace S) × CircleSpace S) :=
    htR.isTopologicalAddGroup
  letI : ContinuousSMul ℝ ((Y × CircleSpace S) × CircleSpace S) := htR.continuousSMul
  letI : LocallyConvexSpace ℝ ((Y × CircleSpace S) × CircleSpace S) := htR.toLocallyConvexSpace
  have herror := smoothTameOn_comp_generic hp htp htR
    (smoothTameOn_prodMk_generic hp htp
      (smoothTameOn_prodMk_generic hp htp hparameter hc) hi) he
    (fun x hx => ⟨⟨hmap hx, mem_univ _⟩, mem_univ _⟩)
  have heven := smoothTameOn_postcompose_generic hp htp htc herror
    (circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)))
    (circleModelEvenProjection_isTame (hS.2.1 (3 / 4 : ℝ)))
  exact solve_smoothTameOn_codRestrict (evenCircleSubmodule S)
    (solve_isClosed_evenCircle hS) heven
    (fun x => coupledEvenProjectionCLM hS (error ((parameter x, circle x), inverse x)))
    (fun x _ => coupledEvenProjectionCLM_val hS _)

end GenericAssembly

section ProductAssembly

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {p : ℕ → Seminorm ℝ E} {U : Set E}

private theorem coupled_error_source_product
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone (pairGrading (pairGrading p (residualGrading S)) (residualGrading S)))
    (htp : WithSeminorms (pairGrading (pairGrading p (residualGrading S)) (residualGrading S)))
    (htq : WithSeminorms p) (hU : IsOpen U)
    {a : E → ℝ} {t : E → CoupledWeakHeight S}
    {height : E × ResidualSpace S → HeightPair S}
    {error : (E × CircleSpace S) × HeightPair S → S.Source}
    (ha : SmoothTameOn p realGrading U a)
    (ht : SmoothTameOn p (coupledWeakHeightGrading S) U t)
    (hh : SmoothTameOn (pairGrading p (residualGrading S)) (heightPairGrading S)
      (U ×ˢ univ) height)
    (he : SmoothTameOn
      (pairGrading (pairGrading p (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
      S.sourceGrading ((U ×ˢ univ) ×ˢ univ) error) :
    SmoothTameOn (pairGrading (pairGrading p (residualGrading S)) (residualGrading S))
      S.sourceGrading ((U ×ˢ univ) ×ˢ univ)
      (fun z : (E × ResidualSpace S) × ResidualSpace S =>
        a z.1.1 • coupledScalarTypeErrorSourceLinear hD hT hS (t z.1.1) z.1.2.1.val
            (height (z.1.1, z.2)) + error ((z.1.1, z.1.2.2.val), height (z.1.1, z.2))) := by
  letI := htp.isTopologicalAddGroup
  letI := htp.continuousSMul
  have hproj := coupled_error_product_projections (p := p) (q := residualGrading S) hU
  exact coupled_error_source_assemble hD hT hS hp htp htq hproj.1
    (coupled_error_ignore_right (residualGrading S)
      (coupled_error_ignore_right (residualGrading S) ha))
    (coupled_error_ignore_right (residualGrading S)
      (coupled_error_ignore_right (residualGrading S) ht))
    (coupled_error_subtype_smoothTameOn (q := scalarHeightGrading S) S.Q.toLinearMap.ker
      (coupled_error_fst_smoothTameOn hproj.2))
    (coupled_error_forget_middle hh)
    (coupled_error_subtype_smoothTameOn (q := (S.circle (3 / 4 : ℝ)).grading)
      (evenCircleSubmodule S) (coupled_error_snd_smoothTameOn hproj.2))
    he (fun z hz => hz.1.1)

private theorem coupled_error_even_product
    (hS : IsPhysicalSpaces D T S)
    (hp : Monotone (pairGrading (pairGrading p (residualGrading S)) (residualGrading S)))
    (htp : WithSeminorms (pairGrading (pairGrading p (residualGrading S)) (residualGrading S)))
    (htq : WithSeminorms p) (hU : IsOpen U)
    {inverse : E × ResidualSpace S → CircleSpace S}
    {error : (E × CircleSpace S) × CircleSpace S → CircleSpace S}
    (hi : SmoothTameOn (pairGrading p (residualGrading S)) (S.circle (3 / 4 : ℝ)).grading
      (U ×ˢ univ) inverse)
    (he : SmoothTameOn
      (pairGrading (pairGrading p (S.circle (3 / 4 : ℝ)).grading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading ((U ×ˢ univ) ×ˢ univ) error) :
    SmoothTameOn (pairGrading (pairGrading p (residualGrading S)) (residualGrading S))
      (evenCircleGradingAt S (3 / 4 : ℝ)) ((U ×ˢ univ) ×ˢ univ)
      (fun z : (E × ResidualSpace S) × ResidualSpace S =>
        coupledEvenProjectionCLM hS (error ((z.1.1, z.1.2.2.val), inverse (z.1.1, z.2)))) := by
  letI := htp.isTopologicalAddGroup
  letI := htp.continuousSMul
  have hproj := coupled_error_product_projections (p := p) (q := residualGrading S) hU
  exact coupled_error_even_assemble hS hp htp htq hproj.1
    (coupled_error_subtype_smoothTameOn (q := (S.circle (3 / 4 : ℝ)).grading)
      (evenCircleSubmodule S) (coupled_error_snd_smoothTameOn hproj.2))
    (coupled_error_forget_middle hi) he (fun z hz => hz.1.1)

end ProductAssembly

private theorem coupled_error_source_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (V : CoupledInverseData S)
    (typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S)
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (htype : SmoothTameOn (coupledErrorParameterGrading S) (coupledWeakHeightGrading S) U
      (fun z => typeCoefficient (liftSectorParameter S C z)))
    (hheight : SmoothTameOn (coupledErrorSingleInputGrading S) (heightPairGrading S)
      (U ×ˢ univ) (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (V.V (liftSectorParameter S C z.1) z.2).1))
    (hLerror : SmoothTameOn (coupledErrorHeightActionGrading S) S.sourceGrading
      ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
        L.error (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    SmoothTameOn (coupledErrorFullInputGrading S) S.sourceGrading ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S =>
        z.1.1.2 • coupledScalarTypeErrorSourceLinear hD hT hS
            (typeCoefficient (liftSectorParameter S C z.1.1)) z.1.2.1.val
            (V.V (liftSectorParameter S C z.1.1) z.2).1 +
          L.error (liftSectorParameter S C z.1.1) z.1.2.2.val
            (V.V (liftSectorParameter S C z.1.1) z.2).1) := by
  have hg := coupled_error_grading_facts S
  have h := coupled_error_source_product (D := D) (T := T) (S := S)
    (E := StateDirections S × ℝ) (p := coupledErrorParameterGrading S) (U := U)
    (a := fun z : StateDirections S × ℝ => z.2)
    (t := fun z : StateDirections S × ℝ => typeCoefficient (liftSectorParameter S C z))
    (height := fun z : (StateDirections S × ℝ) × ResidualSpace S =>
      (V.V (liftSectorParameter S C z.1) z.2).1)
    (error := fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
      L.error (liftSectorParameter S C z.1.1) z.1.2 z.2)
    hD hT hS hg.1 hg.2.1 hg.2.2 hU
    (coupled_error_scale_smoothTameOn S hU) htype hheight hLerror
  exact h

private theorem coupled_error_even_smoothTameOn
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (hinverse : SmoothTameOn (coupledErrorSingleInputGrading S)
      (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        R.inverse (z.2.2.val - z.1.2 • B.heightRow (liftSectorParameter S C z.1)
          (V.V (liftSectorParameter S C z.1) z.2).1 -
          B.circleColumn (liftSectorParameter S C z.1)
            (V.V (liftSectorParameter S C z.1) z.2).2.2.1)))
    (hRerror : SmoothTameOn (coupledErrorCircleActionGrading S)
      (S.circle (3 / 4 : ℝ)).grading ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S =>
        R.error (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    SmoothTameOn (coupledErrorFullInputGrading S) (evenCircleGradingAt S (3 / 4 : ℝ))
      ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S =>
        coupledEvenProjectionCLM hS
          (R.error (liftSectorParameter S C z.1.1) z.1.2.2.val
            (R.inverse (z.2.2.val - z.1.1.2 •
              B.heightRow (liftSectorParameter S C z.1.1)
                (V.V (liftSectorParameter S C z.1.1) z.2).1 -
              B.circleColumn (liftSectorParameter S C z.1.1)
                (V.V (liftSectorParameter S C z.1.1) z.2).2.2.1)))) := by
  have hg := coupled_error_grading_facts S
  have h := coupled_error_even_product (D := D) (T := T) (S := S)
    (E := StateDirections S × ℝ) (p := coupledErrorParameterGrading S) (U := U)
    (inverse := fun z : (StateDirections S × ℝ) × ResidualSpace S =>
      R.inverse (z.2.2.val - z.1.2 • B.heightRow (liftSectorParameter S C z.1)
        (V.V (liftSectorParameter S C z.1) z.2).1 -
        B.circleColumn (liftSectorParameter S C z.1)
          (V.V (liftSectorParameter S C z.1) z.2).2.2.1))
    (error := fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S =>
      R.error (liftSectorParameter S C z.1.1) z.1.2 z.2)
    hS hg.1 hg.2.1 hg.2.2 hU hinverse hRerror
  exact h

theorem coupledQuadraticErrorData_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S)
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (htype : SmoothTameOn (coupledErrorParameterGrading S)
      (coupledWeakHeightGrading S) U
      (fun z => typeCoefficient (liftSectorParameter S C z)))
    (hheight : SmoothTameOn
      (coupledErrorSingleInputGrading S)
      (heightPairGrading S) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (V.V (liftSectorParameter S C z.1) z.2).1))
    (hinverse : SmoothTameOn
      (coupledErrorSingleInputGrading S)
      (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        R.inverse (z.2.2.val - z.1.2 • B.heightRow (liftSectorParameter S C z.1)
          (V.V (liftSectorParameter S C z.1) z.2).1 -
          B.circleColumn (liftSectorParameter S C z.1)
            (V.V (liftSectorParameter S C z.1) z.2).2.2.1)))
    (hLerror : SmoothTameOn
      (coupledErrorHeightActionGrading S)
      S.sourceGrading ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
        L.error (liftSectorParameter S C z.1.1) z.1.2 z.2))
    (hRerror : SmoothTameOn
      (coupledErrorCircleActionGrading S)
      (S.circle (3 / 4 : ℝ)).grading ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S =>
        R.error (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    SmoothTameOn
      (coupledErrorFullInputGrading S)
      (residualGrading S) ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S =>
        (coupledQuadraticErrorData hD hT hS R L B V typeCoefficient).Q
          (liftSectorParameter S C z.1.1) z.1.2 z.2) := by
  have hg := coupled_error_grading_facts S
  letI := hg.2.1.isTopologicalAddGroup
  letI := hg.2.1.continuousSMul
  have hscalar := coupled_error_source_smoothTameOn hD hT hS C L V typeCoefficient
    hU htype hheight hLerror
  have heven := coupled_error_even_smoothTameOn hS C R B V hU hinverse hRerror
  apply smoothTameOn_congr (smoothTameOn_prodMk_generic hg.1 hg.2.1 hscalar heven)
  intro z hz
  apply Prod.ext
  · exact (coupledQuadraticErrorData_scalar hD hT hS R L B V typeCoefficient
      (liftSectorParameter S C z.1.1) z.1.2 z.2).symm
  · exact (coupledQuadraticErrorData_circle hD hT hS R L B V typeCoefficient
      (liftSectorParameter S C z.1.1) z.1.2 z.2).symm

end ContinuousFlexibility.Statements
