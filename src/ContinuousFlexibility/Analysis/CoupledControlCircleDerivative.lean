module

public import ContinuousFlexibility.Analysis.CoupledControlCircleInverse
public import ContinuousFlexibility.Analysis.CoupledCircleParameterIndependence
public import ContinuousFlexibility.Analysis.CoupledTameDerivative
public import ContinuousFlexibility.Analysis.SolveNewtonBridge
public import ContinuousFlexibility.Analysis.SolveStateSpaces
public import ContinuousFlexibility.Scalar.WeightedStateTopology

/-!
# Smooth tame control and height rows from the actual residual

Both rows are restrictions of one genuine first derivative of the N08
residual. The constant control and height insertions preserve their given
gradings. In particular the height row is used with its actual factor `q`;
no regularity of the separately divided row at `q = 0` is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section AbstractRows

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

private theorem coupled_row_pair_inl_grading
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (n : ℕ) (x : E) :
    pairGrading p q n (x, 0) = p n x := by
  simp only [pairGrading_apply, map_zero, add_zero]

private theorem coupled_row_control_grading
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (n : ℕ) (u : F) :
    pairGrading p (pairGrading realGrading (pairGrading q q)) n
      (0, (0, (u, 0))) = q n u := by
  simp only [pairGrading_apply, map_zero, add_zero, zero_add]

private theorem coupled_row_zero_odd (L : E →ₗ[ℝ] (ℕ → ℝ → ℝ)) (m : ℕ) (θ : ℝ) :
    L 0 m (-θ) = -L 0 m θ := by
  simp only [map_zero, Pi.zero_apply, neg_zero]

private theorem coupled_row_inl_bound
    (L : E →L[ℝ] F) (p : ℕ → Seminorm ℝ F) (q : ℕ → Seminorm ℝ E)
    (hL : ∀ n u, p n (L u) ≤ q n u) :
    ∀ n u, pairGrading p realGrading n
      (((ContinuousLinearMap.inl ℝ F ℝ).comp L) u) ≤ q n u := by
  intro n u
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    pairGrading_apply, map_zero, add_zero] using hL n u

private theorem coupled_row_output_bound
    (W : Submodule ℝ F) (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    ∀ n (y : E × W), q n ((W.subtypeL.comp (ContinuousLinearMap.snd ℝ E W)) y) ≤
      1 * pairGrading p (fun n => (q n).comp W.subtype) n y := by
  intro n y
  change q n y.2.val ≤ 1 * (p n y.1 + q n y.2.val)
  have hb : q n y.2.val ≤ p n y.1 + q n y.2.val :=
    le_add_of_nonneg_left (apply_nonneg (p n) y.1)
  exact hb.trans_eq (one_mul _).symm

end AbstractRows

private theorem coupled_row_derivative_smooth
    {X Y E Z : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {r : ℕ → Seminorm ℝ E} {s : ℕ → Seminorm ℝ Z}
    {U : Set X} {f : X → Y}
    (hp : Monotone p) (htp : WithSeminorms p)
    (J : SmoothDirections U f) (hJ : J.TameBounds p q)
    (L : E →L[ℝ] X) (hL : ∀ n u, p n (L u) ≤ r n u)
    (out : Y →L[ℝ] Z) (hout : ∀ n y, s n (out y) ≤ 1 * q n y) :
    SmoothTameOn (pairGrading p r) s (U ×ˢ univ)
      (fun z : X × E => out (J.D 1 z.1 (fun _ => L z.2))) := by
  have hd := smoothTameOn_derivativeEvaluation hp htp J hJ
  let Li : (X × E) →L[ℝ] (X × X) :=
    (ContinuousLinearMap.fst ℝ X E).prod (L.comp (ContinuousLinearMap.snd ℝ X E))
  have hLi (z : X × E) : Li z = (z.1, L z.2) := rfl
  have hLib : ∀ n z, pairGrading p p n (Li z) ≤ 1 * pairGrading p r n z := by
    intro n z
    simpa only [hLi, pairGrading_apply, one_mul] using
      add_le_add (le_rfl : p n z.1 ≤ p n z.1) (hL n z.2)
  have hpre := solve_smoothTameOn_precomp hd Li (A := 1) le_rfl hLib
  have hdom : Li ⁻¹' (U ×ˢ univ) = U ×ˢ univ := by
    ext z
    simp only [mem_preimage, hLi, mem_prod, mem_univ, and_true]
  rw [hdom] at hpre
  simpa only [hLi] using solve_smoothTameOn_postcomp hpre out zero_le_one hout

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
    (coupledSectorHeightLinear S η).val = (η, (0, (0, 0))) := rfl

theorem coupledSectorHeightLinear_eq (S : PhysicalSpacesData) (η : HeightPair S) :
    coupledSectorHeightLinear S η = coupledSectorHeightDirection S η := by
  apply Subtype.ext
  exact (coupledSectorHeightLinear_val S η).trans (coupledSectorHeightDirection_val S η).symm

theorem coupledSectorHeightLinear_grading (S : PhysicalSpacesData)
    (n : ℕ) (η : HeightPair S) :
    sectorGrading S n (coupledSectorHeightLinear S η) = heightPairGrading S n η := by
  change stateGrading S n (coupledSectorHeightLinear S η).val = _
  exact (congrArg (stateGrading S n) (coupledSectorHeightLinear_val S η)).trans
    (coupled_row_pair_inl_grading (heightPairGrading S)
      (pairGrading realGrading (pairGrading (S.circle (3 / 4 : ℝ)).grading
        (S.circle (3 / 4 : ℝ)).grading)) n η)

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
    coupledControlStateLinear hS u = (0, (0, (u.val, 0))) := rfl

/-- Constant controls are genuine tangent vectors of the frozen sector. -/
def coupledSectorControlLinear
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) :
    CoupledConstantCircle hS →L[ℝ] StateDirections S :=
  (coupledControlStateLinear hS).codRestrict (stateSectorSubmodule S) (by
    intro u
    change stateSector S (coupledControlStateLinear hS u)
    exact (congrArg (stateSector S) (coupledControlStateLinear_apply hS u)).mpr
      ⟨coupledConstantCircle_constant hS u,
        coupled_row_zero_odd (S.circle (3 / 4 : ℝ)).decode⟩)

theorem coupledSectorControlLinear_val
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (u : CoupledConstantCircle hS) :
    (coupledSectorControlLinear hS u).val = (0, (0, (u.val, 0))) :=
  coupledControlStateLinear_apply hS u

theorem coupledSectorControlLinear_grading
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (n : ℕ) (u : CoupledConstantCircle hS) :
    sectorGrading S n (coupledSectorControlLinear hS u) =
      coupledConstantCircleGrading hS n u := by
  change stateGrading S n (coupledSectorControlLinear hS u).val =
    (S.circle (3 / 4 : ℝ)).grading n u.val
  exact (congrArg (stateGrading S n) (coupledSectorControlLinear_val hS u)).trans
    (coupled_row_control_grading (heightPairGrading S) (S.circle (3 / 4 : ℝ)).grading n u.val)

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
  let J : SmoothDirections U (sectorJointResidual S C P) := hres.choose
  have hJ : J.TameBounds a (residualGrading S) := hres.choose_spec
  let L₀ : E →L[ℝ] (StateDirections S × ℝ) :=
    (ContinuousLinearMap.inl ℝ (StateDirections S) ℝ).comp L
  have hL₀ : ∀ n u, a n (L₀ u) ≤ p n u :=
    coupled_row_inl_bound L (sectorGrading S) p hL
  let out : ResidualSpace S →L[ℝ] CircleSpace S :=
    (evenCircleSubmodule S).subtypeL.comp
      (ContinuousLinearMap.snd ℝ S.Source (EvenCircle S))
  have houtb : ∀ n y, (S.circle (3 / 4 : ℝ)).grading n (out y) ≤
      1 * residualGrading S n y :=
    coupled_row_output_bound (evenCircleSubmodule S) S.sourceGrading
      (S.circle (3 / 4 : ℝ)).grading
  have hpost := coupled_row_derivative_smooth ha hta J hJ L₀ hL₀ out houtb
  apply smoothTameOn_congr hpost
  intro z hz
  change (J.D 1 z.1 (fun _ => (L z.2, (0 : ℝ)))).2.val = row z.1 z.2
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
    (fun z η => z.2 • B.heightRow (liftSectorParameter S C z) η)
  intro z hz η
  exact h8.2.2.2.2.2.2.2.2.2.1 (liftSectorParameter S C z)
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
    (fun z u => B.circleColumn (liftSectorParameter S C z) u.val)
  intro z hz u
  exact h8.2.2.2.2.2.2.2.2.2.2.1 (liftSectorParameter S C z)
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
    exact (coupled_circleAngularMeanProjection_grading_le hS n u).trans_eq (one_mul _).symm
  apply smoothTameOn_congr
    (solve_smoothTameOn_postcomp hc (coupledConstantCircleProjection hS) zero_le_one hmean)
  intro z _
  apply Subtype.ext
  exact (coupledConstantCircleProjection_val hS
    (B.circleColumn (liftSectorParameter S C z.1) z.2.val)).trans
      (coupledControlCircleOperator_val hS B (liftSectorParameter S C z.1) z.2).symm

/-- The reciprocal diagonal is a smooth tame family on the original N08
sector neighborhood. Its continuity and derivative tower are conclusions. -/
theorem coupledControlCircleInverse_smoothTameOn_of_n08
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (coupledConstantCircleGrading hM))
      (coupledConstantCircleGrading hM)
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle hM =>
        coupledControlCircleInverse hM B
          (liftSectorParameter S C z.1) z.2) := by
  let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
  have hU := h8.2.1
  have hrestriction := h8.2.2.2.2.2.1
  have hcolumn := h8.2.2.2.2.2.2.2.2.2.2.2.1
  have hdiag := h8.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hJ := h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlo := h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hH (m : ℕ) : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT h1.1.1.choose_spec.2.1 m)).2.1
  have hz {z : StateDirections S × ℝ} (h : z ∈ sectorNeighborhood S base ε ε) :
      liftSectorParameter S C z ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood h le_rfl
  have hs (z : StateDirections S × ℝ) : stateSector S (liftSectorParameter S C z).1 :=
    h1.2.2.1.liftSectorParameter_sector z
  exact coupledControlCircleInverse_smoothTameOn hM B
    (liftSectorParameter S C)
    (tamePairGrading_monotone (solve_sectorGrading_monotone S) weighted_realGrading_monotone)
    (withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
      weighted_realGrading_withSeminorms) hU hrestriction hH
    (fun z h => hcolumn _ (hz h) (hs z))
    (fun z h => hdiag _ (hz h) (hs z))
    (fun z h => hJ _ (hz h) (hs z))
    (fun z h m => (hlo _ (hz h) (hs z) m).1)
    (coupledControlCircleOperator_smoothTameOn_of_n08 hM h1.2.2.1 h8)

end ContinuousFlexibility.Statements
