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
set_option backward.isDefEq.respectTransparency.types false

section GenericProjections

variable {X E F : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ E} {r : ℕ → Seminorm ℝ F}
  {U : Set X}

private theorem coupled_regular_fst_smoothTameOn {f : X → E × F}
    (hf : SmoothTameOn p (pairGrading q r) U f) :
    SmoothTameOn p q U (fun x => (f x).1) := by
  exact solve_smoothTameOn_postcomp hf (ContinuousLinearMap.fst ℝ E F)
    (B := 1) zero_le_one (fun n y => by
      change q n y.1 ≤ 1 * (q n y.1 + r n y.2)
      simpa only [one_mul] using le_add_of_nonneg_right (apply_nonneg (r n) y.2))

private theorem coupled_regular_snd_smoothTameOn {f : X → E × F}
    (hf : SmoothTameOn p (pairGrading q r) U f) :
    SmoothTameOn p r U (fun x => (f x).2) := by
  exact solve_smoothTameOn_postcomp hf (ContinuousLinearMap.snd ℝ E F)
    (B := 1) zero_le_one (fun n y => by
      change r n y.2 ≤ 1 * (q n y.1 + r n y.2)
      simpa only [one_mul] using le_add_of_nonneg_left (apply_nonneg (q n) y.1))

private theorem coupled_regular_subtype_smoothTameOn
    (W : Submodule ℝ E) {f : X → W}
    (hf : SmoothTameOn p (fun n => (q n).comp W.subtype) U f) :
    SmoothTameOn p q U (fun x => (f x).val) := by
  exact solve_smoothTameOn_postcomp hf W.subtypeL (B := 1) zero_le_one (fun n y => by
    change q n y.val ≤ 1 * q n y.val
    exact le_of_eq (one_mul _).symm)

private theorem coupled_regular_mean_smoothTameOn
    {T : MaterialData} {γ : ℝ} {M : CircleModelData} (hM : IsCircleModel T γ M)
    {f : X → M.Space} (hf : SmoothTameOn p M.grading U f) :
    SmoothTameOn p (coupledConstantCircleGrading hM) U
      (fun x => coupledConstantCircleProjection hM (f x)) := by
  exact solve_smoothTameOn_postcomp hf (coupledConstantCircleProjection hM)
    (B := 1) zero_le_one (fun n u => by
      change M.grading n (coupledConstantCircleProjection hM u).val ≤ 1 * M.grading n u
      exact (coupled_circleAngularMeanProjection_grading_le hM n u).trans_eq
        (one_mul _).symm)

end GenericProjections

section GenericParameterComposition

variable {X Y E : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {bond : ∀ n, F (n + 1) →L[ℝ] F n}

private theorem coupled_regular_parameterApply_smoothTameOn
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ E}
    {s : ℕ → Seminorm ℝ (ProjectiveLimit F bond)}
    (hp : Monotone p) (htp : WithSeminorms p)
    (htq : WithSeminorms q) (htr : WithSeminorms r)
    {U : Set X} {V : Set Y} {parameter : X → Y} {value : X → E}
    {f : Y × E → ProjectiveLimit F bond}
    (hz : SmoothTameOn p q U parameter) (hv : SmoothTameOn p r U value)
    (hf : SmoothTameOn (pairGrading q r) s (V ×ˢ univ) f)
    (hmap : MapsTo parameter U V) :
    SmoothTameOn p s U (fun x => f (parameter x, value x)) := by
  letI : IsTopologicalAddGroup X := htp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := htp.continuousSMul
  letI : IsTopologicalAddGroup Y := htq.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := htq.continuousSMul
  letI : IsTopologicalAddGroup E := htr.isTopologicalAddGroup
  letI : ContinuousSMul ℝ E := htr.continuousSMul
  have htqr := withSeminorms_pairGrading htq htr
  letI : LocallyConvexSpace ℝ (Y × E) := htqr.toLocallyConvexSpace
  exact smoothTameOn_comp_generic hp htp htqr
    (smoothTameOn_prodMk_generic hp htp hz hv) hf
    (fun x hx => ⟨hmap hx, mem_univ _⟩)

end GenericParameterComposition

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

private abbrev coupledRegularParameterGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ (StateDirections S × ℝ) :=
  pairGrading (sectorGrading S) realGrading

private abbrev coupledRegularInputGrading (S : PhysicalSpacesData) :=
  pairGrading (coupledRegularParameterGrading S) (residualGrading S)

private theorem coupled_regular_gradings (S : PhysicalSpacesData) :
    Monotone (coupledRegularInputGrading S) ∧
      WithSeminorms (coupledRegularInputGrading S) ∧
      WithSeminorms (coupledRegularParameterGrading S) := by
  have hp : Monotone (coupledRegularParameterGrading S) := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms (coupledRegularParameterGrading S) := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  exact ⟨tamePairGrading_monotone hp (coupled_residualGrading_monotone S),
    withSeminorms_pairGrading htp (coupled_residualGrading_withSeminorms S), htp⟩

private theorem coupled_regular_parameter_smoothTameOn (hU : IsOpen U) :
    SmoothTameOn (coupledRegularInputGrading S) (coupledRegularParameterGrading S)
      (U ×ˢ univ) (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.1) := by
  have hDom : IsOpen (U ×ˢ (univ : Set (ResidualSpace S))) := hU.prod isOpen_univ
  exact smoothTameOn_continuousLinear_on hDom
    (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) (ResidualSpace S))
    (scalar_pair_fst_isTame (coupledRegularParameterGrading S) (residualGrading S))

private theorem coupled_regular_residual_smoothTameOn (hU : IsOpen U) :
    SmoothTameOn (coupledRegularInputGrading S) (residualGrading S)
      (U ×ˢ univ) (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2) := by
  have hDom : IsOpen (U ×ˢ (univ : Set (ResidualSpace S))) := hU.prod isOpen_univ
  exact smoothTameOn_continuousLinear_on hDom
    (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) (ResidualSpace S))
    (scalar_pair_snd_isTame (coupledRegularParameterGrading S) (residualGrading S))

private theorem coupled_regular_source_smoothTameOn (hU : IsOpen U) :
    SmoothTameOn (coupledRegularInputGrading S) S.sourceGrading
      (U ×ˢ univ) (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2.1) :=
  coupled_regular_fst_smoothTameOn (coupled_regular_residual_smoothTameOn (S := S) hU)

private theorem coupled_regular_circle_smoothTameOn (hU : IsOpen U) :
    SmoothTameOn (coupledRegularInputGrading S) (S.circle (3 / 4 : ℝ)).grading
      (U ×ˢ univ) (fun z : (StateDirections S × ℝ) × ResidualSpace S => z.2.2.val) :=
  coupled_regular_subtype_smoothTameOn (q := (S.circle (3 / 4 : ℝ)).grading)
    (evenCircleSubmodule S)
    (coupled_regular_snd_smoothTameOn (coupled_regular_residual_smoothTameOn (S := S) hU))

private theorem coupled_regular_scalarFree_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hG : ScalarInverseProperties D S C L G base ε)
    (hU : IsOpen U) (hsub : U ⊆ sectorNeighborhood S base ε ε) :
    SmoothTameOn (coupledRegularInputGrading S)
      (pairGrading (heightPairGrading S) realGrading) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        G.G (liftSectorParameter S C z.1) z.2.1) := by
  have hg := coupled_regular_gradings S
  have htps := withSeminorms_pairGrading hg.2.2 (coupled_sourceGrading_withSeminorms S)
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × S.Source) := htps.toLocallyConvexSpace
  have hGs := smoothTameOn_mono hG.2.2.2
    (hU.prod (isOpen_univ : IsOpen (univ : Set S.Source)))
    (Set.prod_mono hsub (subset_refl _))
  exact coupled_smoothTameOn_comp_scalarOutput hS hg.1 hg.2.1 htps
    (smoothTameOn_prodMk_generic hg.1 hg.2.1
      (coupled_regular_parameter_smoothTameOn (S := S) hU) (coupled_regular_source_smoothTameOn (S := S) hU))
    hGs (fun z hz => ⟨hz.1, mem_univ _⟩)

private theorem coupled_regular_row_smoothTameOn
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hU : IsOpen U) (hsub : U ⊆ sectorNeighborhood S base ε ε)
    {η : (StateDirections S × ℝ) × ResidualSpace S → HeightPair S}
    (hη : SmoothTameOn (coupledRegularInputGrading S) (heightPairGrading S) (U ×ˢ univ) η) :
    SmoothTameOn (coupledRegularInputGrading S) (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        z.1.2 • B.heightRow (liftSectorParameter S C z.1) (η z)) := by
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  have hg := coupled_regular_gradings S
  have hrow := smoothTameOn_mono (coupled_scaledHeightRow_smoothTameOn hRef h8)
    (hU.prod (isOpen_univ : IsOpen (univ : Set (HeightPair S))))
    (Set.prod_mono hsub (subset_refl _))
  exact coupled_regular_parameterApply_smoothTameOn hg.1 hg.2.1 hg.2.2
    (coupled_heightPairGrading_withSeminorms S)
    (coupled_regular_parameter_smoothTameOn (S := S) hU) hη hrow (fun z hz => hz.1)

private theorem coupled_regular_control_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hU : IsOpen U) (hsub : U ⊆ sectorNeighborhood S base ε ε)
    (hcontrol : SmoothTameOn
      (pairGrading (coupledRegularParameterGrading S) (coupledConstantCircleGrading hM))
      (coupledConstantCircleGrading hM) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle hM =>
        coupledConstantFeedbackInverse hM B G (liftSectorParameter S C z.1) z.2)) :
    SmoothTameOn (coupledRegularInputGrading S) (coupledConstantCircleGrading hM) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryConstantControl hM B G (liftSectorParameter S C z.1) z.2) := by
  have hg := coupled_regular_gradings S
  have htpk := withSeminorms_pairGrading hg.2.2 (coupledConstantCircleGrading_withSeminorms hM)
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × CoupledConstantCircle hM) :=
    htpk.toLocallyConvexSpace
  have hfree := coupled_regular_scalarFree_smoothTameOn hS hG hU hsub
  have hrow := coupled_regular_row_smoothTameOn hM hRef h8 hU hsub
    (coupled_regular_fst_smoothTameOn hfree)
  have heffective := coupled_smoothTameOn_sub hg.1
    (coupled_regular_circle_smoothTameOn (S := S) hU) hrow
  have hmean := coupled_regular_mean_smoothTameOn hM heffective
  exact coupled_smoothTameOn_comp_constantCircle hM hg.1 hg.2.1 htpk
    (smoothTameOn_prodMk_generic hg.1 hg.2.1
      (coupled_regular_parameter_smoothTameOn (S := S) hU) hmean)
    hcontrol (fun z hz => ⟨hz.1, mem_univ _⟩)

private theorem coupled_regular_height_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hU : IsOpen U) (hsub : U ⊆ sectorNeighborhood S base ε ε)
    (hκ : SmoothTameOn (coupledRegularInputGrading S) (coupledConstantCircleGrading hM)
      (U ×ˢ univ) (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryConstantControl hM B G (liftSectorParameter S C z.1) z.2)) :
    SmoothTameOn (coupledRegularInputGrading S)
      (pairGrading (heightPairGrading S) realGrading) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryHeightFormula hM B G (liftSectorParameter S C z.1) z.2) := by
  have hg := coupled_regular_gradings S
  have htk := coupledConstantCircleGrading_withSeminorms hM
  letI : LocallyConvexSpace ℝ (CoupledConstantCircle hM) := htk.toLocallyConvexSpace
  have htpc := withSeminorms_pairGrading hg.2.2 coupled_controlGrading_withSeminorms
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × ControlBanach) :=
    htpc.toLocallyConvexSpace
  have htps := withSeminorms_pairGrading hg.2.2 (coupled_sourceGrading_withSeminorms S)
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × S.Source) := htps.toLocallyConvexSpace
  let hρ := coupled_continuousLinear_to_norm_isTame
    (coupledConstantCircleGrading_monotone hM) htk (coupledConstantControlRestriction hM B)
  have hξ := coupled_smoothTameOn_comp_banach hg.1 hg.2.1 htk hκ
    (smoothTameOn_continuousLinear (coupledConstantControlRestriction hM B) hρ.choose_spec)
    (fun _ _ => mem_univ _)
  have hcolumn := smoothTameOn_mono
    h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    (hU.prod (isOpen_univ : IsOpen (univ : Set ControlBanach)))
    (Set.prod_mono hsub (subset_refl _))
  have hsource := coupled_smoothTameOn_comp_source hS hg.1 hg.2.1 htpc
    (smoothTameOn_prodMk_generic hg.1 hg.2.1
      (coupled_regular_parameter_smoothTameOn (S := S) hU) hξ)
    hcolumn (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hGs := smoothTameOn_mono hG.2.2.2
    (hU.prod (isOpen_univ : IsOpen (univ : Set S.Source)))
    (Set.prod_mono hsub (subset_refl _))
  have hG1 := coupled_smoothTameOn_comp_scalarOutput hS hg.1 hg.2.1 htps
    (smoothTameOn_prodMk_generic hg.1 hg.2.1
      (coupled_regular_parameter_smoothTameOn (S := S) hU) hsource)
    hGs (fun z hz => ⟨hz.1, mem_univ _⟩)
  exact coupled_smoothTameOn_sub hg.1
    (coupled_regular_scalarFree_smoothTameOn hS hG hU hsub) hG1

private theorem coupled_regular_remainder_smoothTameOn
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hU : IsOpen U) (hsub : U ⊆ sectorNeighborhood S base ε ε)
    (hκ : SmoothTameOn (coupledRegularInputGrading S) (coupledConstantCircleGrading hM)
      (U ×ˢ univ) (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryConstantControl hM B G (liftSectorParameter S C z.1) z.2))
    (hheight : SmoothTameOn (coupledRegularInputGrading S)
      (pairGrading (heightPairGrading S) realGrading) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryHeightFormula hM B G (liftSectorParameter S C z.1) z.2)) :
    SmoothTameOn (coupledRegularInputGrading S) (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        coupledRecoveryRemainderFormula hM B G (liftSectorParameter S C z.1) z.2) := by
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  have hg := coupled_regular_gradings S
  have hrow := coupled_regular_row_smoothTameOn hM hRef h8 hU hsub
    (coupled_regular_fst_smoothTameOn hheight)
  have hcolumn := smoothTameOn_mono (coupled_constantCircleColumn_smoothTameOn hM hRef h8)
    (hU.prod (isOpen_univ : IsOpen (univ : Set (CoupledConstantCircle hM))))
    (Set.prod_mono hsub (subset_refl _))
  have hcolumnκ := coupled_regular_parameterApply_smoothTameOn hg.1 hg.2.1 hg.2.2
    (coupledConstantCircleGrading_withSeminorms hM)
    (coupled_regular_parameter_smoothTameOn (S := S) hU) hκ hcolumn (fun z hz => hz.1)
  exact coupled_smoothTameOn_sub hg.1
    (coupled_smoothTameOn_sub hg.1 (coupled_regular_circle_smoothTameOn (S := S) hU) hrow) hcolumnκ

private theorem coupled_regular_chart_smoothTameOn
    (hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hU : IsOpen U)
    (hinverse : ∃ l b, IsTameLinear (S.circle (3 / 4 : ℝ)).grading
      (S.circle (3 / 4 : ℝ)).grading R.inverse l b)
    (hchart : SmoothTameOn
      (pairGrading (coupledRegularParameterGrading S) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CircleSpace S =>
        R.chartIncrement (liftSectorParameter S C z.1) z.2))
    {f : (StateDirections S × ℝ) × ResidualSpace S → CircleSpace S}
    (hf : SmoothTameOn (coupledRegularInputGrading S) (S.circle (3 / 4 : ℝ)).grading
      (U ×ˢ univ) f) :
    SmoothTameOn (coupledRegularInputGrading S) (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        R.chartIncrement (liftSectorParameter S C z.1) (R.inverse (f z))) := by
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  have hg := coupled_regular_gradings S
  have htc : WithSeminorms (S.circle (3 / 4 : ℝ)).grading := withSeminorms_graded _ _
  have hc : Monotone (S.circle (3 / 4 : ℝ)).grading := gradedSeminorm_monotone _ _
  let hi := hinverse.choose_spec.choose_spec
  let Inv : CircleSpace S →L[ℝ] CircleSpace S := hi.toContinuousLinearMap htc htc hc
  have hInv := smoothTameOn_congr
    (smoothTameOn_postcompose_generic hg.1 hg.2.1 htc hf Inv hi)
    (fun z _ => IsTameLinear.toContinuousLinearMap_apply hi htc htc hc (f z))
  exact coupled_regular_parameterApply_smoothTameOn hg.1 hg.2.1 hg.2.2 htc
    (coupled_regular_parameter_smoothTameOn (S := S) hU) hInv hchart (fun z hz => hz.1)

theorem coupledRecoveryRegularFormula_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hU : IsOpen U) (hsub : U ⊆ sectorNeighborhood S base ε ε)
    (hinverse : ∃ l b, IsTameLinear (S.circle (3 / 4 : ℝ)).grading
      (S.circle (3 / 4 : ℝ)).grading R.inverse l b)
    (hcontrol :
      let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
      SmoothTameOn
        (pairGrading (pairGrading (sectorGrading S) realGrading)
          (coupledConstantCircleGrading hM))
        (coupledConstantCircleGrading hM) (U ×ˢ univ)
        (fun z : (StateDirections S × ℝ) × CoupledConstantCircle hM =>
          coupledConstantFeedbackInverse hM B G
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
  let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
  have hg := coupled_regular_gradings S
  have hκ := coupled_regular_control_smoothTameOn hS hM hRef hG h8 hU hsub hcontrol
  have hheight := coupled_regular_height_smoothTameOn hS hM hG h8 hU hsub hκ
  have hrem := coupled_regular_remainder_smoothTameOn hM hRef h8 hU hsub hκ hheight
  have hchartOut := coupled_regular_chart_smoothTameOn hM hU hinverse hchart hrem
  have hκval := coupled_regular_subtype_smoothTameOn
    (q := (S.circle (3 / 4 : ℝ)).grading) (coupledConstantCircleSubmodule hM) hκ
  exact smoothTameOn_prodMk_generic hg.1 hg.2.1
    (coupled_regular_fst_smoothTameOn hheight)
    (smoothTameOn_prodMk_generic hg.1 hg.2.1
      (coupled_regular_snd_smoothTameOn hheight)
      (smoothTameOn_prodMk_generic hg.1 hg.2.1 hκval hchartOut))

private theorem coupled_recoveredSectorV_eq_regularFormula
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (hsmall : ‖z.2 • controlFeedback S B G (liftSectorParameter S C z)‖ < (1 / 2 : ℝ))
    (y : ResidualSpace S) :
    ((coupledRecoveredInverseData hT hS h1 h2 h8).sectorV z y).val =
      coupledRecoveryRegularFormula (hS.2.1 (3 / 4 : ℝ)) B G
        (liftSectorParameter S C z) y R := by
  have hvalid : CoupledRecoveryValid S C B G base ε (liftSectorParameter S C z) :=
    ⟨liftSectorParameter_mem_stateNeighborhood hz le_rfl,
      h1.2.2.1.liftSectorParameter_sector z, hsmall⟩
  have hvalue : ((coupledRecoveredInverseData hT hS h1 h2 h8).sectorV z y).val =
      coupledRecoveredV hS h8 (liftSectorParameter S C z) y :=
    coupledRecoveredInverseData_sectorV hT hS h1 h2 h8 z y
  exact hvalue.trans (coupledRecoveryRegularFormula_eq_recoveredV hT hS h1 h8 hvalid y).symm

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
    (hcontrol :
      let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
      SmoothTameOn
        (pairGrading (pairGrading (sectorGrading S) realGrading)
          (coupledConstantCircleGrading hM))
        (coupledConstantCircleGrading hM) (U ×ˢ univ)
        (fun z : (StateDirections S × ℝ) × CoupledConstantCircle hM =>
          coupledConstantFeedbackInverse hM B G
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
  exact solve_smoothTameOn_codRestrict
    (X := (StateDirections S × ℝ) × ResidualSpace S) (Y := AnnularState S)
    (stateSectorSubmodule S) h8.1
    (coupledRecoveryRegularFormula_smoothTameOn hS h1.2.2.1 hG h8 hU hsub
      h2.2.2.2.2.2.2.2.2.2.1 hcontrol hchart)
    (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
      (coupledRecoveredInverseData hT hS h1 h2 h8).sectorV z.1 z.2)
    (fun z hz => coupled_recoveredSectorV_eq_regularFormula hT hS h1 h2 h8
      (hsub hz.1) (hsmall z.1 hz.1) z.2)

end ContinuousFlexibility.Statements
