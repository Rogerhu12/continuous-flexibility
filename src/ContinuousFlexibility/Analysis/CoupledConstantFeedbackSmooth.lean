import ContinuousFlexibility.Analysis.CoupledConstantFeedbackInverse
import ContinuousFlexibility.Analysis.CoupledControlCircleDerivative
import ContinuousFlexibility.Analysis.CoupledControlResponseSmooth
import ContinuousFlexibility.Analysis.CoupledPhysicalTameComposition

/-!
# The actual constant-circle forward feedback is smooth tame

The forward family is assembled from the scalar response, the genuine
scaled height derivative, angular averaging and the circle control
derivative. The restriction into the control Banach space uses its actual
finite-order continuity bound.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section AbstractFeedback

variable {X E H : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {bond : ∀ n, F (n + 1) →L[ℝ] F n}

private theorem coupled_feedback_response_comp
    {p : ℕ → Seminorm ℝ X} {r : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ H}
    {s : ℕ → Seminorm ℝ (ProjectiveLimit F bond)}
    (hp : Monotone p) (htp : WithSeminorms p)
    (hr : Monotone r) (htr : WithSeminorms r) (htq : WithSeminorms q)
    {U : Set X} (hU : IsOpen U)
    {response : X → E → H} {row : X → H → ProjectiveLimit F bond}
    (hresponse : SmoothTameOn (pairGrading p r) q (U ×ˢ univ)
      (fun z : X × E => response z.1 z.2))
    (hrow : SmoothTameOn (pairGrading p q) s (U ×ˢ univ)
      (fun z : X × H => row z.1 z.2)) :
    SmoothTameOn (pairGrading p r) s (U ×ˢ univ)
      (fun z : X × E => row z.1 (response z.1 z.2)) := by
  have hpr := tamePairGrading_monotone hp hr
  have htpr := withSeminorms_pairGrading htp htr
  have htpq := withSeminorms_pairGrading htp htq
  letI : LocallyConvexSpace ℝ (X × H) := htpq.toLocallyConvexSpace
  have hfst : SmoothTameOn (pairGrading p r) p (U ×ˢ univ) (fun z : X × E => z.1) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ X E) (scalar_pair_fst_isTame p r)
  have hin := smoothTameOn_prodMk_generic hpr htpr hfst hresponse
  exact smoothTameOn_comp_generic hpr htpr htpq hin hrow
    (fun z hz => ⟨hz.1, mem_univ _⟩)

private theorem coupled_feedback_control_input
    {Uc : Type*} [NormedAddCommGroup Uc] [NormedSpace ℝ Uc]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ E}
    (hp : Monotone p) (htp : WithSeminorms p)
    (hq : Monotone q) (htq : WithSeminorms q)
    {U : Set X} (hU : IsOpen U) (ρ : E →L[ℝ] Uc) :
    SmoothTameOn (pairGrading p q) (pairGrading p (fun _ => normSeminorm ℝ Uc))
      (U ×ˢ univ) (fun z : X × E => (z.1, ρ z.2)) := by
  have hpq := tamePairGrading_monotone hp hq
  have htpq := withSeminorms_pairGrading htp htq
  let L : (X × E) →L[ℝ] Uc := ρ.comp (ContinuousLinearMap.snd ℝ X E)
  have hbound := coupled_continuousLinear_to_norm_isTame hpq htpq L
  have hρ : SmoothTameOn (pairGrading p q) (fun _ => normSeminorm ℝ Uc)
      (U ×ˢ univ) (fun z : X × E => ρ z.2) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ) L hbound.choose_spec
  have hfst : SmoothTameOn (pairGrading p q) p (U ×ˢ univ) (fun z : X × E => z.1) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ X E) (scalar_pair_fst_isTame p q)
  exact smoothTameOn_prodMk_generic hpq htpq hfst hρ

private theorem coupled_feedback_forward_difference
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ E}
    (hp : Monotone p) (htp : WithSeminorms p)
    (hq : Monotone q) (htq : WithSeminorms q)
    (e : E ≃L[ℝ] ProjectiveLimit F bond)
    {U : Set X} (hU : IsOpen U) (ρ : E →L[ℝ] ControlBanach)
    {operator : X → E → E} {response : X → ControlBanach → E}
    (hoperator : SmoothTameOn (pairGrading p q) q (U ×ˢ univ)
      (fun z : X × E => operator z.1 z.2))
    (hresponse : SmoothTameOn (pairGrading p controlGrading) q (U ×ˢ univ)
      (fun z : X × ControlBanach => response z.1 z.2)) :
    SmoothTameOn (pairGrading p q) q (U ×ˢ univ)
      (fun z : X × E => operator z.1 z.2 - response z.1 (ρ z.2)) := by
  have hpq : Monotone (pairGrading p q) := tamePairGrading_monotone hp hq
  have htpq : WithSeminorms (pairGrading p q) := withSeminorms_pairGrading htp htq
  have htpc : WithSeminorms (pairGrading p controlGrading) :=
    withSeminorms_pairGrading htp coupled_controlGrading_withSeminorms
  letI : LocallyConvexSpace ℝ (X × ControlBanach) := htpc.toLocallyConvexSpace
  have hin := coupled_feedback_control_input hp htp hq htq hU ρ
  have hr := coupled_smoothTameOn_comp_equiv hpq htpq htpc e hin hresponse
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  exact coupled_smoothTameOn_sub hpq hoperator hr

end AbstractFeedback

private theorem coupled_feedback_mean_bound
    {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hM : IsCircleModel T γ M) (n : ℕ) (u : M.Space) :
    coupledConstantCircleGrading hM n (coupledConstantCircleProjection hM u) ≤
      1 * M.grading n u :=
  (coupled_circleAngularMeanProjection_grading_le hM n u).trans_eq (one_mul _).symm

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

theorem coupled_scaledHeightControlResponse_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach =>
        z.1.2 • B.heightRow (liftSectorParameter S C z.1)
          (controlHeightResponse S B G (liftSectorParameter S C z.1) z.2)) := by
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.2.1 (3 / 4 : ℝ)).2.1 n).isComplete.completeSpace_coe
  exact coupled_feedback_response_comp
    (F := fun n => ↥((S.circle (3 / 4 : ℝ)).level n))
    (bond := (S.circle (3 / 4 : ℝ)).bond)
    (p := pairGrading (sectorGrading S) realGrading)
    (r := controlGrading) (q := heightPairGrading S) (s := (S.circle (3 / 4 : ℝ)).grading)
    (response := fun z u => controlHeightResponse S B G (liftSectorParameter S C z) u)
    (row := fun z η => z.2 • B.heightRow (liftSectorParameter S C z) η)
    (tamePairGrading_monotone (solve_sectorGrading_monotone S) weighted_realGrading_monotone)
    (withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
      weighted_realGrading_withSeminorms)
    coupled_controlGrading_monotone coupled_controlGrading_withSeminorms
    (coupled_heightPairGrading_withSeminorms S) h8.2.1
    (coupled_controlHeightResponse_smoothTameOn hS h8.2.1
      h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hG.2.2.2)
    (coupled_scaledHeightRow_smoothTameOn hRef h8)

theorem coupledConstantHeightResponse_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
      (coupledConstantCircleGrading hM)
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach =>
        coupledConstantHeightResponse hM B G
          (liftSectorParameter S C z.1) z.2) := by
  let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
  have hr := coupled_scaledHeightControlResponse_smoothTameOn hS hRef hG h8
  apply smoothTameOn_congr
    (solve_smoothTameOn_postcomp hr (coupledConstantCircleProjection hM) zero_le_one
      (coupled_feedback_mean_bound hM))
  intro z _
  exact (coupledConstantHeightResponse_apply hM B G
    (liftSectorParameter S C z.1) z.2).symm

theorem coupledConstantFeedbackOperator_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (coupledConstantCircleGrading hM))
      (coupledConstantCircleGrading hM)
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle hM =>
        coupledConstantFeedbackOperator hM B G
          (liftSectorParameter S C z.1) z.2) := by
  let hM : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    (hM.2.1 n).isComplete.completeSpace_coe
  letI : ∀ n, CompleteSpace ↥(subLevel (coupledConstantCircleSubmodule hM) n) := fun n =>
    subLevel_completeSpace (coupledConstantCircleSubmodule hM) n
  have h := coupled_feedback_forward_difference
    (p := pairGrading (sectorGrading S) realGrading)
    (q := coupledConstantCircleGrading hM)
    (operator := fun z u => coupledControlCircleOperator hM B (liftSectorParameter S C z) u)
    (response := fun z u => coupledConstantHeightResponse hM B G (liftSectorParameter S C z) u)
    (tamePairGrading_monotone (solve_sectorGrading_monotone S) weighted_realGrading_monotone)
    (withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
      weighted_realGrading_withSeminorms)
    (coupledConstantCircleGrading_monotone hM) (coupledConstantCircleGrading_withSeminorms hM)
    (subspaceEquiv (coupledConstantCircleSubmodule hM) (coupledConstantCircle_isClosed hM))
    h8.2.1 (coupledConstantControlRestriction hM B)
    (coupledControlCircleOperator_smoothTameOn_of_n08 hM hRef h8)
    (coupledConstantHeightResponse_smoothTameOn hS hRef hG h8)
  apply smoothTameOn_congr h
  intro z hz
  exact (coupledConstantFeedbackOperator_apply hM B G
    (liftSectorParameter S C z.1) z.2).symm

end ContinuousFlexibility.Statements
