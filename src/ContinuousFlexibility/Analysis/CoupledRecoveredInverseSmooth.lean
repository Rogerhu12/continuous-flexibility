import ContinuousFlexibility.Analysis.CoupledRecoveredInverseFormula
import ContinuousFlexibility.Analysis.CoupledConstantFeedbackSmooth
import ContinuousFlexibility.Analysis.SolveTameSubspace

/-!
# Smooth tameness of the same recovered coupled inverse

The constant-circle inverse supplies the recovered control, whose actual
weighted mean is then used in the scalar inverse. The residual chart
increment is composed last. The regular formula is identified with the
existing guarded recovery before restricting its codomain to the sector.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ} {U : Set (StateDirections S × ℝ)}

private theorem coupled_residualGrading_monotone (S : PhysicalSpacesData) :
    Monotone (residualGrading S) :=
  tamePairGrading_monotone
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)
    (fun _ _ h u => gradedSeminorm_monotone _ _ h u.val)

private theorem coupled_residualGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (residualGrading S) :=
  withSeminorms_pairGrading (coupled_sourceGrading_withSeminorms S)
    ((Topology.IsInducing.subtypeVal).withSeminorms
      (f := (evenCircleSubmodule S).subtype) (withSeminorms_graded _ _))

theorem coupledRecoveryRegularFormula_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hU : IsOpen U) (hsub : U ⊆ sectorNeighborhood S base ε ε)
    (hinverse : ∃ l b, IsTameLinear (S.circle (3 / 4 : ℝ)).grading
      (S.circle (3 / 4 : ℝ)).grading R.inverse l b)
    (hcontrol : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ))))
      (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ))) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle (hS.2.1 (3 / 4 : ℝ)) =>
        coupledConstantFeedbackInverse (hS.2.1 (3 / 4 : ℝ)) B G
          (liftSectorParameter S C z.1) z.2))
    (hchart : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CircleSpace S =>
        R.chartIncrement (liftSectorParameter S C z.1) z.2)) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (stateGrading S) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryRegularFormula (hS.2.1 (3 / 4 : ℝ)) B G
          (liftSectorParameter S C z.1) z.2 R) := by
  let hM := hS.2.1 (3 / 4 : ℝ)
  let p := pairGrading (sectorGrading S) realGrading
  let a := pairGrading p (residualGrading S)
  let c := (S.circle (3 / 4 : ℝ)).grading
  let k := coupledConstantCircleGrading hM
  let o := pairGrading (heightPairGrading S) realGrading
  have hp : Monotone p := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms p := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have ha : Monotone a := tamePairGrading_monotone hp (coupled_residualGrading_monotone S)
  have hta : WithSeminorms a := withSeminorms_pairGrading htp
    (coupled_residualGrading_withSeminorms S)
  have htc : WithSeminorms c := withSeminorms_graded _ _
  have htk : WithSeminorms k := coupledConstantCircleGrading_withSeminorms hM
  have htps := withSeminorms_pairGrading htp (coupled_sourceGrading_withSeminorms S)
  have htph := withSeminorms_pairGrading htp (coupled_heightPairGrading_withSeminorms S)
  have htpc := withSeminorms_pairGrading htp htc
  have htpk := withSeminorms_pairGrading htp htk
  have hDom := hU.prod isOpen_univ
  have hsubDom : U ×ˢ (univ : Set S.Source) ⊆ sectorNeighborhood S base ε ε ×ˢ univ :=
    Set.prod_mono hsub (subset_refl _)
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  have hz : SmoothTameOn a p (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.1) :=
    smoothTameOn_continuousLinear_on hDom
      (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) (ResidualSpace S))
      (scalar_pair_fst_isTame p (residualGrading S))
  have hy : SmoothTameOn a (residualGrading S) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2) :=
    smoothTameOn_continuousLinear_on hDom
      (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) (ResidualSpace S))
      (scalar_pair_snd_isTame p (residualGrading S))
  have hySource : SmoothTameOn a S.sourceGrading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2.1) :=
    solve_smoothTameOn_postcomp hy (ContinuousLinearMap.fst ℝ S.Source (EvenCircle S))
      (B := 1) zero_le_one (fun n y => by
        change S.sourceGrading n y.1 ≤ 1 *
          (S.sourceGrading n y.1 + (S.circle (3 / 4 : ℝ)).grading n y.2.val)
        simpa only [one_mul] using le_add_of_nonneg_right
          (apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) y.2.val))
  let LC : ResidualSpace S →L[ℝ] CircleSpace S :=
    (evenCircleSubmodule S).subtypeL.comp (ContinuousLinearMap.snd ℝ S.Source (EvenCircle S))
  have hLC (y : ResidualSpace S) : LC y = y.2.val := by
    rw [LC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', Submodule.subtypeL_apply]
  have hyCircle : SmoothTameOn a c (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2.2.val) := by
    have hc := solve_smoothTameOn_postcomp hy LC (B := 1) zero_le_one (fun n y => by
      rw [hLC, one_mul]
      exact le_add_of_nonneg_left (apply_nonneg (S.sourceGrading n) y.1))
    exact smoothTameOn_congr hc (fun z _ => hLC z.2)
  have hGs := smoothTameOn_mono hG.2.2.2 (hU.prod isOpen_univ) hsubDom
  have hG0 : SmoothTameOn a o (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        G.G (liftSectorParameter S C z.1) z.2.1) :=
    coupled_smoothTameOn_comp_scalarOutput hS ha hta htps
      (smoothTameOn_prodMk_generic ha hta hz hySource) hGs
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hη0 := solve_smoothTameOn_postcomp hG0 (ContinuousLinearMap.fst ℝ (HeightPair S) ℝ)
    (r := heightPairGrading S) (B := 1) zero_le_one (fun n y => by
      simpa only [ContinuousLinearMap.coe_fst', pairGrading_apply, one_mul] using
        le_add_of_nonneg_right (apply_nonneg (realGrading n) y.2))
  have hrow := smoothTameOn_mono (coupled_scaledHeightRow_smoothTameOn hRef h8)
    (hU.prod isOpen_univ) (Set.prod_mono hsub (subset_refl _))
  have hrow0 := smoothTameOn_comp_generic ha hta htph
    (smoothTameOn_prodMk_generic ha hta hz hη0) hrow
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  have heffective := coupled_smoothTameOn_sub ha hyCircle hrow0
  have hmean := solve_smoothTameOn_postcomp heffective (coupledConstantCircleProjection hM)
    (r := k) (B := 1) zero_le_one (fun n u => by
      change (S.circle (3 / 4 : ℝ)).grading n (coupledConstantCircleProjection hM u).val ≤ _
      rw [coupledConstantCircleProjection_val, one_mul]
      exact circleAngularMeanLinear_grading_le hM n u)
  have hκ : SmoothTameOn a k (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryConstantControl hM B G (liftSectorParameter S C z.1) z.2) :=
    coupled_smoothTameOn_comp_constantCircle hM ha hta htpk
      (smoothTameOn_prodMk_generic ha hta hz hmean) hcontrol
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  obtain ⟨bρ, hρ⟩ := coupled_continuousLinear_to_norm_isTame
    (coupledConstantCircleGrading_monotone hM) htk (coupledConstantControlRestriction hM B)
  have hξ := coupled_smoothTameOn_comp_banach ha hta htk hκ
    (smoothTameOn_continuousLinear (coupledConstantControlRestriction hM B) hρ)
    (fun _ _ => mem_univ _)
  have hcolumn := smoothTameOn_mono
    h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (hU.prod isOpen_univ)
    (Set.prod_mono hsub (subset_refl _))
  have hsource := coupled_smoothTameOn_comp_source hS ha hta
    (withSeminorms_pairGrading htp coupled_controlGrading_withSeminorms)
    (smoothTameOn_prodMk_generic ha hta hz hξ) hcolumn
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hG1 := coupled_smoothTameOn_comp_scalarOutput hS ha hta htps
    (smoothTameOn_prodMk_generic ha hta hz hsource) hGs
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hheight : SmoothTameOn a o (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryHeightFormula hM B G (liftSectorParameter S C z.1) z.2) :=
    coupled_smoothTameOn_sub ha hG0 hG1
  have hη := solve_smoothTameOn_postcomp hheight (ContinuousLinearMap.fst ℝ (HeightPair S) ℝ)
    (r := heightPairGrading S) (B := 1) zero_le_one (fun n y => by
      simpa only [ContinuousLinearMap.coe_fst', pairGrading_apply, one_mul] using
        le_add_of_nonneg_right (apply_nonneg (realGrading n) y.2))
  have hμ := solve_smoothTameOn_postcomp hheight (ContinuousLinearMap.snd ℝ (HeightPair S) ℝ)
    (r := realGrading) (B := 1) zero_le_one (fun n y => by
      simpa only [ContinuousLinearMap.coe_snd', pairGrading_apply, one_mul] using
        le_add_of_nonneg_left (apply_nonneg (heightPairGrading S n) y.1))
  have hκval := solve_smoothTameOn_postcomp hκ (coupledConstantCircleSubmodule hM).subtypeL
    (r := c) (B := 1) zero_le_one (fun n u => by
      change (S.circle (3 / 4 : ℝ)).grading n u.val ≤ 1 * (S.circle (3 / 4 : ℝ)).grading n u.val
      rw [one_mul])
  have hrowη := smoothTameOn_comp_generic ha hta htph
    (smoothTameOn_prodMk_generic ha hta hz hη) hrow
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hcircleColumn := smoothTameOn_mono (coupled_constantCircleColumn_smoothTameOn hM hRef h8)
    (hU.prod isOpen_univ) (Set.prod_mono hsub (subset_refl _))
  have hcolumnκ := smoothTameOn_comp_generic ha hta htpk
    (smoothTameOn_prodMk_generic ha hta hz hκ) hcircleColumn
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hrem : SmoothTameOn a c (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryRemainderFormula hM B G (liftSectorParameter S C z.1) z.2) :=
    coupled_smoothTameOn_sub ha (coupled_smoothTameOn_sub ha hyCircle hrowη) hcolumnκ
  obtain ⟨li, bi, hi⟩ := hinverse
  let Inv : CircleSpace S →L[ℝ] CircleSpace S :=
    hi.toContinuousLinearMap htc htc (gradedSeminorm_monotone _ _)
  have hInv := smoothTameOn_comp_generic ha hta htc hrem
    (smoothTameOn_continuousLinear Inv hi) (fun _ _ => mem_univ _)
  have hchartOut := smoothTameOn_comp_generic ha hta htpc
    (smoothTameOn_prodMk_generic ha hta hz hInv) hchart
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  exact smoothTameOn_prodMk_generic ha hta hη
    (smoothTameOn_prodMk_generic ha hta hμ
      (smoothTameOn_prodMk_generic ha hta hκval hchartOut))

/-- The conclusion uses the previously defined guarded inverse and its
previously defined sector restriction. -/
theorem coupledRecoveredInverseData_smoothTameOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hU : IsOpen U) (hsub : U ⊆ sectorNeighborhood S base ε ε)
    (hsmall : ∀ z ∈ U,
      ‖z.2 • controlFeedback S B G (liftSectorParameter S C z)‖ < (1 / 2 : ℝ))
    (hcontrol : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ))))
      (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ))) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle (hS.2.1 (3 / 4 : ℝ)) =>
        coupledConstantFeedbackInverse (hS.2.1 (3 / 4 : ℝ)) B G
          (liftSectorParameter S C z.1) z.2))
    (hchart : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CircleSpace S =>
        R.chartIncrement (liftSectorParameter S C z.1) z.2)) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (sectorGrading S) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (coupledRecoveredInverseData hT hS h1 h2 h8).sectorV z.1 z.2) := by
  have hformula := coupledRecoveryRegularFormula_smoothTameOn hS h1.2.2.1 hG h8 hU hsub
    h2.2.2.2.2.2.2.2.2.2.1 hcontrol hchart
  apply solve_smoothTameOn_codRestrict (stateSectorSubmodule S) h8.1 hformula
  intro z hz
  rw [coupledRecoveredInverseData_sectorV hT hS h1 h2 h8 z.1 z.2]
  change coupledRecoveredV hS h8 (liftSectorParameter S C z.1) z.2 = _
  exact (coupledRecoveryRegularFormula_eq_recoveredV hT hS h1 h8
    ⟨liftSectorParameter_mem_stateNeighborhood (hsub hz.1) le_rfl,
      h1.2.2.1.liftSectorParameter_sector z.1, hsmall z.1 hz.1⟩ z.2).symm

end ContinuousFlexibility.Statements
