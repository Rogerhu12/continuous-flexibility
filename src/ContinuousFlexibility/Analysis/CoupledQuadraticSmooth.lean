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

section Projections

variable {E F Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

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

theorem coupledQuadraticErrorData_smoothTameOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S)
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    (htype : SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (coupledWeakHeightGrading S) U
      (fun z => typeCoefficient (liftSectorParameter S C z)))
    (hheight : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (heightPairGrading S) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (V.V (liftSectorParameter S C z.1) z.2).1))
    (hinverse : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        R.inverse (z.2.2.val - z.1.2 • B.heightRow (liftSectorParameter S C z.1)
          (V.V (liftSectorParameter S C z.1) z.2).1 -
          B.circleColumn (liftSectorParameter S C z.1)
            (V.V (liftSectorParameter S C z.1) z.2).2.2.1)))
    (hLerror : SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
      S.sourceGrading ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
        L.error (liftSectorParameter S C z.1.1) z.1.2 z.2))
    (hRerror : SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S =>
        R.error (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (residualGrading S)) (residualGrading S))
      (residualGrading S) ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S =>
        (coupledQuadraticErrorData hD hT hS R L B V typeCoefficient).Q
          (liftSectorParameter S C z.1.1) z.1.2 z.2) := by
  let p := pairGrading (sectorGrading S) realGrading
  let r := residualGrading S
  let c := (S.circle (3 / 4 : ℝ)).grading
  let a := pairGrading p r
  let b := pairGrading a r
  let W : Set (((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S) :=
    (U ×ˢ univ) ×ˢ univ
  have hp : Monotone p := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms p := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have hr : Monotone r := tamePairGrading_monotone
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)
  have htr : WithSeminorms r := withSeminorms_pairGrading
    (coupled_sourceGrading_withSeminorms S)
    ((Topology.IsInducing.subtypeVal).withSeminorms
      (f := (evenCircleSubmodule S).subtype) (withSeminorms_graded _ _))
  have hb : Monotone b := tamePairGrading_monotone (tamePairGrading_monotone hp hr) hr
  have htb : WithSeminorms b := withSeminorms_pairGrading
    (withSeminorms_pairGrading htp htr) htr
  have htc : WithSeminorms c := withSeminorms_graded _ _
  have hW : IsOpen W := (hU.prod isOpen_univ).prod isOpen_univ
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.2.1 (3 / 4 : ℝ)).2.1 n).isComplete.completeSpace_coe
  have hzr : SmoothTameOn b a W
      (fun z : ((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S => z.1) :=
    smoothTameOn_continuousLinear_on hW
      (ContinuousLinearMap.fst ℝ ((StateDirections S × ℝ) × ResidualSpace S) (ResidualSpace S))
      (scalar_pair_fst_isTame a r)
  have hz := solve_smoothTameOn_postcomp hzr
    (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) (ResidualSpace S))
    (r := p) (B := 1) zero_le_one (fun n z => by
      change p n z.1 ≤ 1 * (p n z.1 + r n z.2)
      simpa only [one_mul] using le_add_of_nonneg_right (apply_nonneg (r n) z.2))
  have hs := solve_smoothTameOn_postcomp hzr
    (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) (ResidualSpace S))
    (r := r) (B := 1) zero_le_one (fun n z => by
      change r n z.2 ≤ 1 * (p n z.1 + r n z.2)
      simpa only [one_mul] using le_add_of_nonneg_left (apply_nonneg (p n) z.1))
  have hq := solve_smoothTameOn_postcomp hz
    (ContinuousLinearMap.snd ℝ (StateDirections S) ℝ)
    (r := realGrading) (B := 1) zero_le_one (fun n z => by
      change realGrading n z.2 ≤ 1 * (sectorGrading S n z.1 + realGrading n z.2)
      simpa only [one_mul] using
        le_add_of_nonneg_left (apply_nonneg (sectorGrading S n) z.1))
  let source : ResidualSpace S →L[ℝ] ScalarHeightSpace S :=
    S.Q.toLinearMap.ker.subtypeL.comp (ContinuousLinearMap.fst ℝ S.Source (EvenCircle S))
  have hsource := solve_smoothTameOn_postcomp hs source
    (r := scalarHeightGrading S) (B := 1) zero_le_one (fun n y => by
      change (S.height (3 / 4 : ℝ)).grading n y.1.val ≤
        1 * (S.sourceGrading n y.1 + c n y.2.val)
      simpa only [one_mul] using le_add_of_nonneg_right (apply_nonneg (c n) y.2.val))
  let circle : ResidualSpace S →L[ℝ] CircleSpace S :=
    (evenCircleSubmodule S).subtypeL.comp
      (ContinuousLinearMap.snd ℝ S.Source (EvenCircle S))
  have hcircle := solve_smoothTameOn_postcomp hs circle
    (r := c) (B := 1) zero_le_one (fun n y => by
      change c n y.2.val ≤ 1 * (S.sourceGrading n y.1 + c n y.2.val)
      simpa only [one_mul] using le_add_of_nonneg_left (apply_nonneg (S.sourceGrading n) y.1))
  have ht := coupled_error_ignore_right r (coupled_error_ignore_right r htype)
  have hη := coupled_error_forget_middle hheight
  have hψ := coupled_error_forget_middle hinverse
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
  have hscalar := smoothTameOn_add hb hscalar1 hLcomp
  have htR := withSeminorms_pairGrading (withSeminorms_pairGrading htp htc) htc
  letI : LocallyConvexSpace ℝ (((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S) :=
    htR.toLocallyConvexSpace
  have hRcomp := smoothTameOn_comp_generic hb htb htR
    (smoothTameOn_prodMk_generic hb htb hzrc hψ) hRerror
    (fun z hz => ⟨⟨hz.1.1, mem_univ _⟩, mem_univ _⟩)
  have hevenVal := smoothTameOn_postcompose_generic hb htb htc hRcomp
    (circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)))
    (circleModelEvenProjection_isTame (hS.2.1 (3 / 4 : ℝ)))
  have heven := solve_smoothTameOn_codRestrict (evenCircleSubmodule S)
    (solve_isClosed_evenCircle hS) hevenVal
    (fun z => coupledEvenProjectionCLM hS
      (R.error (liftSectorParameter S C z.1.1) z.1.2.2.val
        (R.inverse (z.2.2.val - z.1.1.2 •
          B.heightRow (liftSectorParameter S C z.1.1)
            (V.V (liftSectorParameter S C z.1.1) z.2).1 -
          B.circleColumn (liftSectorParameter S C z.1.1)
            (V.V (liftSectorParameter S C z.1.1) z.2).2.2.1))))
    (fun z _ => coupledEvenProjectionCLM_val hS _)
  apply smoothTameOn_congr (smoothTameOn_prodMk_generic hb htb hscalar heven)
  intro z hz
  apply Prod.ext
  · exact (coupledQuadraticErrorData_scalar hD hT hS R L B V typeCoefficient
      (liftSectorParameter S C z.1.1) z.1.2 z.2).symm
  · exact (coupledQuadraticErrorData_circle hD hT hS R L B V typeCoefficient
      (liftSectorParameter S C z.1.1) z.1.2 z.2).symm

end ContinuousFlexibility.Statements
