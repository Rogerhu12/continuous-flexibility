import ContinuousFlexibility.Analysis.CoupledControlCircleInverse
import ContinuousFlexibility.Analysis.CoupledCircleParameterIndependence
import ContinuousFlexibility.Analysis.CoupledTameDerivative
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Scalar.WeightedStateTopology

/-!
# Smooth tame control and height rows from the actual residual

Both rows are restrictions of one genuine first derivative of the N08
residual. The constant control and height insertions preserve their given
gradings. In particular the height row is used with its actual factor `q`;
no regularity of the separately divided row at `q = 0` is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

/-- The existing height direction, bundled continuously and linearly. -/
def coupledSectorHeightLinear (S : PhysicalSpacesData) :
    HeightPair S →L[ℝ] StateDirections S :=
  (ContinuousLinearMap.inl ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S))).codRestrict
    (stateSectorSubmodule S) (fun η => (coupledSectorHeightDirection S η).property)

theorem coupledSectorHeightLinear_val (S : PhysicalSpacesData) (η : HeightPair S) :
    (coupledSectorHeightLinear S η).val = (η, (0, (0, 0))) := by
  rw [coupledSectorHeightLinear, ContinuousLinearMap.coe_codRestrict_apply,
    ContinuousLinearMap.inl_apply]

theorem coupledSectorHeightLinear_eq (S : PhysicalSpacesData) (η : HeightPair S) :
    coupledSectorHeightLinear S η = coupledSectorHeightDirection S η := by
  apply Subtype.ext
  rw [coupledSectorHeightLinear_val, coupledSectorHeightDirection_val]

theorem coupledSectorHeightLinear_grading (S : PhysicalSpacesData)
    (n : ℕ) (η : HeightPair S) :
    sectorGrading S n (coupledSectorHeightLinear S η) = heightPairGrading S n η := by
  change stateGrading S n (coupledSectorHeightLinear S η).val = _
  rw [coupledSectorHeightLinear_val]
  simp only [stateGrading, pairGrading_apply, map_zero, add_zero]

private def coupledControlStateLinear
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) :
    CoupledConstantCircle hS →L[ℝ] AnnularState S :=
  (0 : CoupledConstantCircle hS →L[ℝ] HeightPair S).prod
    ((0 : CoupledConstantCircle hS →L[ℝ] ℝ).prod
      ((coupledConstantCircleSubmodule hS).subtypeL.prod
        (0 : CoupledConstantCircle hS →L[ℝ] CircleSpace S)))

private theorem coupledControlStateLinear_apply
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (u : CoupledConstantCircle hS) :
    coupledControlStateLinear hS u = (0, (0, (u.val, 0))) := by
  simp only [coupledControlStateLinear, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, Submodule.subtypeL_apply]

/-- Constant controls are genuine tangent vectors of the frozen sector. -/
def coupledSectorControlLinear
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) :
    CoupledConstantCircle hS →L[ℝ] StateDirections S :=
  (coupledControlStateLinear hS).codRestrict (stateSectorSubmodule S) (by
    intro u
    rw [coupledControlStateLinear_apply]
    change stateSector S (0, (0, (u.val, 0)))
    refine ⟨coupledConstantCircle_constant hS u, ?_⟩
    intro m θ
    simp only [map_zero, Pi.zero_apply, neg_zero])

theorem coupledSectorControlLinear_val
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (u : CoupledConstantCircle hS) :
    (coupledSectorControlLinear hS u).val = (0, (0, (u.val, 0))) := by
  rw [coupledSectorControlLinear, ContinuousLinearMap.coe_codRestrict_apply,
    coupledControlStateLinear_apply]

theorem coupledSectorControlLinear_grading
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (n : ℕ) (u : CoupledConstantCircle hS) :
    sectorGrading S n (coupledSectorControlLinear hS u) =
      coupledConstantCircleGrading hS n u := by
  change stateGrading S n (coupledSectorControlLinear hS u).val =
    (S.circle (3 / 4 : ℝ)).grading n u.val
  rw [coupledSectorControlLinear_val]
  simp only [stateGrading, pairGrading_apply, map_zero, add_zero, zero_add]

section DirectionalFamily

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- A grading contraction into the sector restricts the actual first
derivative without any loss. The given row is identified by uniqueness of
the genuine directional limit, not by a proposed formal derivative. -/
theorem coupled_circleDirectional_smoothTameOn
    {p : ℕ → Seminorm ℝ E} (L : E →L[ℝ] StateDirections S)
    (hL : ∀ n u, sectorGrading S n (L u) ≤ p n u)
    {U : Set (StateDirections S × ℝ)}
    (hres : SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (residualGrading S) U (sectorJointResidual S C P))
    (row : (StateDirections S × ℝ) → E → CircleSpace S)
    (hrow : ∀ z ∈ U, ∀ u,
      HasProjectiveLineDerivAt (fun x => (P.circle (x, z.2)).val) (row z u)
        (liftSectorParameter S C z).1 (L u).val) :
    SmoothTameOn (pairGrading (pairGrading (sectorGrading S) realGrading) p)
      (S.circle (3 / 4 : ℝ)).grading (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × E => row z.1 z.2) := by
  let a := pairGrading (sectorGrading S) realGrading
  have ha : Monotone a := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have hta : WithSeminorms a := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  obtain ⟨J, hJ⟩ := hres
  have hd := smoothTameOn_derivativeEvaluation ha hta J hJ
  let Li : ((StateDirections S × ℝ) × E) →L[ℝ]
      ((StateDirections S × ℝ) × (StateDirections S × ℝ)) :=
    (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) E).prod
      (((ContinuousLinearMap.inl ℝ (StateDirections S) ℝ).comp L).comp
        (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) E))
  have hLi (z : (StateDirections S × ℝ) × E) : Li z = (z.1, (L z.2, 0)) := by
    simp only [Li, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.inl_apply]
  have hLib : ∀ n z, pairGrading a a n (Li z) ≤ 1 * pairGrading a p n z := by
    intro n z
    rw [hLi, pairGrading_apply, pairGrading_apply, one_mul]
    change a n z.1 + (sectorGrading S n (L z.2) + realGrading n 0) ≤ _
    rw [map_zero, add_zero]
    exact add_le_add le_rfl (hL n z.2)
  have hpre := solve_smoothTameOn_precomp hd Li (A := 1) le_rfl hLib
  have hdom : Li ⁻¹' (U ×ˢ univ) = U ×ˢ univ := by
    ext z
    simp only [mem_preimage, hLi, mem_prod, mem_univ, and_true]
  rw [hdom] at hpre
  let out : ResidualSpace S →L[ℝ] CircleSpace S :=
    (evenCircleSubmodule S).subtypeL.comp
      (ContinuousLinearMap.snd ℝ S.Source (EvenCircle S))
  have hout (y : ResidualSpace S) : out y = y.2.val := by
    simp only [out, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      Submodule.subtypeL_apply]
  have houtb : ∀ n y, (S.circle (3 / 4 : ℝ)).grading n (out y) ≤
      1 * residualGrading S n y := by
    intro n y
    rw [hout, one_mul]
    change (S.circle (3 / 4 : ℝ)).grading n y.2.val ≤
      S.sourceGrading n y.1 + (S.circle (3 / 4 : ℝ)).grading n y.2.val
    exact le_add_of_nonneg_left (apply_nonneg _ _)
  have hpost := solve_smoothTameOn_postcomp hpre out zero_le_one houtb
  apply smoothTameOn_congr hpost
  intro z hz
  rw [hLi, hout]
  have heq := (coupled_circle_first_derivative J hz.1 (L z.2)).unique
    (hrow z.1 hz.1 z.2)
  have hslots : (Fin.cons (L z.2, (0 : ℝ)) Fin.elim0 :
      Fin 1 → StateDirections S × ℝ) = fun _ => (L z.2, 0) := by
    funext i
    fin_cases i
    rfl
  simpa only [projectiveJetHeadLinear_apply, hslots] using heq

end DirectionalFamily

/-- The scaled height row is the actual height derivative, including at
the removable parameter value zero. -/
theorem coupled_scaledHeightRow_smoothTameOn
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (heightPairGrading S))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S =>
        z.1.2 • B.heightRow (liftSectorParameter S C z.1) z.2) := by
  apply coupled_circleDirectional_smoothTameOn (coupledSectorHeightLinear S)
    (fun n u => (coupledSectorHeightLinear_grading S n u).le)
    h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro z hz η
  simpa only [coupledSectorHeightLinear_val, liftSectorParameter] using
    h8.2.2.2.2.2.2.2.2.2.1 (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hRef.liftSectorParameter_sector z) η

/-- The control column is smooth tame when its input is the actual
constant-control sector, with all circle orders retained. -/
theorem coupled_constantCircleColumn_smoothTameOn
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (coupledConstantCircleGrading hS))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle hS =>
        B.circleColumn (liftSectorParameter S C z.1) z.2.val) := by
  apply coupled_circleDirectional_smoothTameOn (coupledSectorControlLinear hS)
    (fun n u => (coupledSectorControlLinear_grading hS n u).le)
    h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro z hz u
  simpa only [coupledSectorControlLinear_val, liftSectorParameter] using
    h8.2.2.2.2.2.2.2.2.2.2.1 (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hRef.liftSectorParameter_sector z) u.val

/-- The forward constant-circle family is the mean of the genuine
control derivative of the N08 residual. -/
theorem coupledControlCircleOperator_smoothTameOn_of_n08
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (coupledConstantCircleGrading hS))
      (coupledConstantCircleGrading hS) (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle hS =>
        coupledControlCircleOperator hS B (liftSectorParameter S C z.1) z.2) := by
  have hc := coupled_constantCircleColumn_smoothTameOn hS hRef h8
  have hmean : ∀ n u, coupledConstantCircleGrading hS n
      (coupledConstantCircleProjection hS u) ≤ 1 * (S.circle (3 / 4 : ℝ)).grading n u := by
    intro n u
    change (S.circle (3 / 4 : ℝ)).grading n (coupledConstantCircleProjection hS u).val ≤ _
    rw [coupledConstantCircleProjection_val, one_mul]
    exact circleAngularMeanLinear_grading_le hS n u
  apply smoothTameOn_congr
    (solve_smoothTameOn_postcomp hc (coupledConstantCircleProjection hS) zero_le_one hmean)
  intro z _
  apply Subtype.ext
  rw [coupledConstantCircleProjection_val, coupledControlCircleOperator_val]

/-- The reciprocal diagonal is a smooth tame family on the original N08
sector neighborhood. Its continuity and derivative tower are conclusions. -/
theorem coupledControlCircleInverse_smoothTameOn_of_n08
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ))))
      (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ)))
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle (hS.2.1 (3 / 4 : ℝ)) =>
        coupledControlCircleInverse (hS.2.1 (3 / 4 : ℝ)) B
          (liftSectorParameter S C z.1) z.2) := by
  have h8' := h8
  obtain ⟨_, hU, _, _, _, hrestriction, _, _, _, _, _, hcolumn, hdiag, _, hJ, hlo, _⟩ := h8'
  have hH (m : ℕ) : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT h1.1.1.choose_spec.2.1 m)).2.1
  have hz {z : StateDirections S × ℝ} (h : z ∈ sectorNeighborhood S base ε ε) :
      liftSectorParameter S C z ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood h le_rfl
  have hs (z : StateDirections S × ℝ) : stateSector S (liftSectorParameter S C z).1 :=
    h1.2.2.1.liftSectorParameter_sector z
  exact coupledControlCircleInverse_smoothTameOn (hS.2.1 (3 / 4 : ℝ)) B
    (liftSectorParameter S C)
    (tamePairGrading_monotone (solve_sectorGrading_monotone S) weighted_realGrading_monotone)
    (withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
      weighted_realGrading_withSeminorms) hU hrestriction hH
    (fun z h => hcolumn _ (hz h) (hs z))
    (fun z h => hdiag _ (hz h) (hs z))
    (fun z h => hJ _ (hz h) (hs z))
    (fun z h m => (hlo _ (hz h) (hs z) m).1)
    (coupledControlCircleOperator_smoothTameOn_of_n08 (hS.2.1 (3 / 4 : ℝ)) h1.2.2.1 h8)

end ContinuousFlexibility.Statements
