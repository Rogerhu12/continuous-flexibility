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
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms p := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have hpc := tamePairGrading_monotone hp coupled_controlGrading_monotone
  have htpc := withSeminorms_pairGrading htp coupled_controlGrading_withSeminorms
  have htph := withSeminorms_pairGrading htp (coupled_heightPairGrading_withSeminorms S)
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.2.1 (3 / 4 : ℝ)).2.1 n).isComplete.completeSpace_coe
  have hresponse := coupled_controlHeightResponse_smoothTameOn hS h8.2.1
    h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hG.2.2.2
  have hfst : SmoothTameOn (pairGrading p controlGrading) p
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach => z.1) :=
    smoothTameOn_continuousLinear_on (h8.2.1.prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) ControlBanach)
      (scalar_pair_fst_isTame p controlGrading)
  have hin := smoothTameOn_prodMk_generic hpc htpc hfst hresponse
  exact smoothTameOn_comp_generic hpc htpc htph hin
    (coupled_scaledHeightRow_smoothTameOn hRef h8) (fun z hz => ⟨hz.1, mem_univ _⟩)

theorem coupledConstantHeightResponse_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
      (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ)))
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach =>
        coupledConstantHeightResponse (hS.2.1 (3 / 4 : ℝ)) B G
          (liftSectorParameter S C z.1) z.2) := by
  have hr := coupled_scaledHeightControlResponse_smoothTameOn hS hRef hG h8
  have hproj : ∀ n u, coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ)) n
      (coupledConstantCircleProjection (hS.2.1 (3 / 4 : ℝ)) u) ≤
        1 * (S.circle (3 / 4 : ℝ)).grading n u := by
    intro n u
    change (S.circle (3 / 4 : ℝ)).grading n
      (coupledConstantCircleProjection (hS.2.1 (3 / 4 : ℝ)) u).val ≤ _
    rw [coupledConstantCircleProjection_val, one_mul]
    exact circleAngularMeanLinear_grading_le (hS.2.1 (3 / 4 : ℝ)) n u
  apply smoothTameOn_congr
    (solve_smoothTameOn_postcomp hr
      (coupledConstantCircleProjection (hS.2.1 (3 / 4 : ℝ))) zero_le_one hproj)
  intro z hz
  exact (coupledConstantHeightResponse_apply (hS.2.1 (3 / 4 : ℝ)) B G
    (liftSectorParameter S C z.1) z.2).symm

theorem coupledConstantFeedbackOperator_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ))))
      (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ)))
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle (hS.2.1 (3 / 4 : ℝ)) =>
        coupledConstantFeedbackOperator (hS.2.1 (3 / 4 : ℝ)) B G
          (liftSectorParameter S C z.1) z.2) := by
  let hM := hS.2.1 (3 / 4 : ℝ)
  let p := pairGrading (sectorGrading S) realGrading
  let k := coupledConstantCircleGrading hM
  have hp : Monotone p := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms p := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have hpk := tamePairGrading_monotone hp (coupledConstantCircleGrading_monotone hM)
  have htpk := withSeminorms_pairGrading htp (coupledConstantCircleGrading_withSeminorms hM)
  let ρ : ((StateDirections S × ℝ) × CoupledConstantCircle hM) →L[ℝ] ControlBanach :=
    (coupledConstantControlRestriction hM B).comp
      (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) (CoupledConstantCircle hM))
  obtain ⟨b, hρ⟩ := coupled_continuousLinear_to_norm_isTame hpk htpk ρ
  have hρsmooth : SmoothTameOn (pairGrading p k) controlGrading
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle hM =>
        coupledConstantControlRestriction hM B z.2) := by
    apply smoothTameOn_congr
      (smoothTameOn_continuousLinear_on (h8.2.1.prod isOpen_univ) ρ hρ)
    intro z hz
    rw [ρ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']
  have hfst : SmoothTameOn (pairGrading p k) p (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle hM => z.1) :=
    smoothTameOn_continuousLinear_on (h8.2.1.prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) (CoupledConstantCircle hM))
      (scalar_pair_fst_isTame p k)
  have hin := smoothTameOn_prodMk_generic hpk htpk hfst hρsmooth
  have hr := coupled_smoothTameOn_comp_constantCircle hM hpk htpk
    (withSeminorms_pairGrading htp coupled_controlGrading_withSeminorms) hin
    (coupledConstantHeightResponse_smoothTameOn hS hRef hG h8)
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hJ := coupledControlCircleOperator_smoothTameOn_of_n08 hM hRef h8
  apply smoothTameOn_congr (coupled_smoothTameOn_sub hpk hJ hr)
  intro z hz
  exact (coupledConstantFeedbackOperator_apply hM B G
    (liftSectorParameter S C z.1) z.2).symm

end ContinuousFlexibility.Statements
