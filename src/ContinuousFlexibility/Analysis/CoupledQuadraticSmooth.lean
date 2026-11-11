import ContinuousFlexibility.Analysis.CoupledQuadraticAlgebra
import ContinuousFlexibility.Analysis.CoupledWeakScalarErrorSmooth
import ContinuousFlexibility.Analysis.CoupledScalarActionSmooth
import ContinuousFlexibility.Analysis.SolveResidualSpaces

/-!
# Joint smooth tameness of the independent coupled error

The coefficient, recovered height, and recovered circle solution are used
on their common parameter neighborhood. Both residual arguments remain
unrestricted. The constructed source and even-circle components retain
their original codomains throughout the composition.
-/

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

private theorem coupled_error_firstInput_smoothTameOn
    (S : PhysicalSpacesData) {U : Set (StateDirections S × ℝ)} (hU : IsOpen U) :
    SmoothTameOn (coupledErrorFullInputGrading S) (coupledErrorSingleInputGrading S)
      ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S => z.1) :=
  smoothTameOn_continuousLinear_on ((hU.prod isOpen_univ).prod isOpen_univ)
    (ContinuousLinearMap.fst ℝ ((StateDirections S × ℝ) × ResidualSpace S) (ResidualSpace S))
    (scalar_pair_fst_isTame (coupledErrorSingleInputGrading S) (residualGrading S))

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
  let r := residualGrading S
  let c := (S.circle (3 / 4 : ℝ)).grading
  have hg := coupled_error_grading_facts S
  have hb := hg.1
  have htb := hg.2.1
  have htp := hg.2.2
  have htc : WithSeminorms c := withSeminorms_graded _ _
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.2.1 (3 / 4 : ℝ)).2.1 n).isComplete.completeSpace_coe
  have hzr := coupled_error_firstInput_smoothTameOn S hU
  have hz := coupled_error_fst_smoothTameOn hzr
  have hs := coupled_error_snd_smoothTameOn hzr
  have hq := coupled_error_snd_smoothTameOn hz
  have hsource := coupled_error_subtype_smoothTameOn
    (q := scalarHeightGrading S) S.Q.toLinearMap.ker (coupled_error_fst_smoothTameOn hs)
  have hcircle := coupled_error_subtype_smoothTameOn
    (q := c) (evenCircleSubmodule S) (coupled_error_snd_smoothTameOn hs)
  have ht := coupled_error_ignore_right r (coupled_error_ignore_right r htype)
  have hη := coupled_error_forget_middle hheight
  have hscalar0 := coupledWeakTypeErrorSourceLinear_smoothTameOn
    hD hT hS hb htb ht hsource hη
  have hscalar1 := coupled_smoothTameOn_source_smul hS hb htb hq hscalar0
  have hzrc := smoothTameOn_prodMk_generic hb htb hz hcircle
  have htL := withSeminorms_pairGrading (withSeminorms_pairGrading htp htc)
    (coupled_heightPairGrading_withSeminorms S)
  letI : LocallyConvexSpace ℝ (((StateDirections S × ℝ) × CircleSpace S) × HeightPair S) :=
    htL.toLocallyConvexSpace
  have hLcomp := coupled_smoothTameOn_comp_source hS hb htb htL
    (smoothTameOn_prodMk_generic hb htb hzrc hη) hLerror
    (fun z hz => ⟨⟨hz.1.1, mem_univ _⟩, mem_univ _⟩)
  exact smoothTameOn_add hb hscalar1 hLcomp

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
  let c := (S.circle (3 / 4 : ℝ)).grading
  have hg := coupled_error_grading_facts S
  have hb := hg.1
  have htb := hg.2.1
  have htp := hg.2.2
  have htc : WithSeminorms c := withSeminorms_graded _ _
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.2.1 (3 / 4 : ℝ)).2.1 n).isComplete.completeSpace_coe
  have hzr := coupled_error_firstInput_smoothTameOn S hU
  have hz := coupled_error_fst_smoothTameOn hzr
  have hs := coupled_error_snd_smoothTameOn hzr
  have hcircle := coupled_error_subtype_smoothTameOn
    (q := c) (evenCircleSubmodule S) (coupled_error_snd_smoothTameOn hs)
  have hψ := coupled_error_forget_middle hinverse
  have hzrc := smoothTameOn_prodMk_generic hb htb hz hcircle
  have htR := withSeminorms_pairGrading (withSeminorms_pairGrading htp htc) htc
  letI : LocallyConvexSpace ℝ (((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S) :=
    htR.toLocallyConvexSpace
  have hRcomp := smoothTameOn_comp_generic hb htb htR
    (smoothTameOn_prodMk_generic hb htb hzrc hψ) hRerror
    (fun z hz => ⟨⟨hz.1.1, mem_univ _⟩, mem_univ _⟩)
  have hevenVal := smoothTameOn_postcompose_generic hb htb htc hRcomp
    (circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)))
    (circleModelEvenProjection_isTame (hS.2.1 (3 / 4 : ℝ)))
  exact solve_smoothTameOn_codRestrict (evenCircleSubmodule S)
    (solve_isClosed_evenCircle hS) hevenVal
    (fun z => coupledEvenProjectionCLM hS
      (R.error (liftSectorParameter S C z.1.1) z.1.2.2.val
        (R.inverse (z.2.2.val - z.1.1.2 •
          B.heightRow (liftSectorParameter S C z.1.1)
            (V.V (liftSectorParameter S C z.1.1) z.2).1 -
          B.circleColumn (liftSectorParameter S C z.1.1)
            (V.V (liftSectorParameter S C z.1.1) z.2).2.2.1))))
    (fun z _ => coupledEvenProjectionCLM_val hS _)

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
