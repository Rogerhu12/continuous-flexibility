import ContinuousFlexibility.Analysis.CoupledFeedbackSmallness
import ContinuousFlexibility.Analysis.CoupledFeedbackRegularization
import ContinuousFlexibility.Analysis.CoupledConstantFeedbackTame
import ContinuousFlexibility.Analysis.CoupledRecoveredInverseSmooth
import ContinuousFlexibility.Analysis.CoupledN09Assembly

/-!
# One common neighborhood for the actual coupled inverse

Feedback smallness and all-order regularization are intersected before any
output order is chosen. The recovered map keeps its original guard; only
the neighborhood in the conclusion is restricted. The remaining chart
input is the smooth tame property of the actual chart increment.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

private theorem coupled_constantFeedbackInverse_tame_on
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {U : Set (StateDirections S × ℝ)} {loss' b : ℕ}
    (hU : IsOpen U) (hsub : U ⊆ sectorNeighborhood S base ε ε)
    (hsmall : ∀ z ∈ U,
      ‖z.2 • controlFeedback S B G (liftSectorParameter S C z)‖ < (1 / 2 : ℝ))
    (hregular : ∀ s, b ≤ s → ∃ c : ℝ, 0 ≤ c ∧ ∀ z ∈ U, ∀ u : ControlBanach,
      (S.circle (3 / 4 : ℝ)).grading s
        (z.2 • B.heightRow (liftSectorParameter S C z)
          (controlHeightResponse S B G (liftSectorParameter S C z) u)) ≤
        c * (1 + pairGrading (sectorGrading S) realGrading (s + loss') z) * ‖u‖) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ))))
      (coupledConstantCircleGrading (hS.2.1 (3 / 4 : ℝ))) (U ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CoupledConstantCircle (hS.2.1 (3 / 4 : ℝ)) =>
        coupledConstantFeedbackInverse (hS.2.1 (3 / 4 : ℝ)) B G
          (liftSectorParameter S C z.1) z.2) := by
  have hRef : referenceStateConditions D S C := h1.2.2.1
  have hstate (z : StateDirections S × ℝ) (hz : z ∈ U) :
      liftSectorParameter S C z ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood (hsub hz) le_rfl
  have hOp := h8.2.2.2.2.2.2.2.2.2.2.2
  have hH (m : ℕ) : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT h1.1.1.choose_spec.2.1 m)).2.1
  have hforward := smoothTameOn_mono
    (coupledConstantFeedbackOperator_smoothTameOn hS hRef hG h8)
    (hU.prod isOpen_univ) (Set.prod_mono hsub (subset_refl _))
  exact coupledConstantFeedbackInverse_smoothTameOn (hS.2.1 (3 / 4 : ℝ)) B G
    (liftSectorParameter S C) (pairGrading (sectorGrading S) realGrading) U
    (fun z hz => hOp.2.1 _ (hstate z hz) (hRef.liftSectorParameter_sector z))
    (fun z hz => hOp.2.2.2.1 _ (hstate z hz) (hRef.liftSectorParameter_sector z))
    (fun z hz => coupledRecovery_diagonal_lower h8 (hstate z hz)
      (hRef.liftSectorParameter_sector z)) hsmall hregular
    (tamePairGrading_monotone (solve_sectorGrading_monotone S) weighted_realGrading_monotone)
    (withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
      weighted_realGrading_withSeminorms) hU h8.2.2.2.2.2.1 hH
    (fun z hz => hOp.1 _ (hstate z hz) (hRef.liftSectorParameter_sector z)) hforward

private theorem coupled_n09Properties_on_subdomain
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {base' : ℕ} {ε' q0 : ℝ} (hqpos : 0 < q0) (hqle : q0 ≤ ε')
    (hsub : coupledNeighborhood S C base' ε' q0 ⊆ stateNeighborhood S C base ε)
    (hsmall : ∀ z ∈ coupledNeighborhood S C base' ε' q0, stateSector S z.1 →
      ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ))
    (htame : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
      (sectorGrading S) (sectorNeighborhood S base' ε' q0 ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ResidualSpace S =>
        (coupledRecoveredInverseData hT hS h1 h2 h8).sectorV z.1 z.2)) :
    N09Properties D T S C R G B (coupledControlInverse S B G)
      (coupledRecoveredInverseData hT hS h1 h2 h8) base' ε' q0 := by
  refine ⟨hqpos, hqle, hsmall, ?_, ?_, ?_, htame⟩
  · intro z hz hs u
    exact ⟨coupledControlInverse_left B G z (hsmall z hz hs) u,
      coupledControlInverse_right B G z (hsmall z hz hs) u⟩
  · intro z hz hs y
    exact coupledRecoveredV_equations hT hS h1 h2 h8
      ⟨hsub hz, hs, hsmall z hz hs⟩ y
  · intro z _ y
    exact coupledRecoveredInverseData_sectorV hT hS h1 h2 h8 z y

/-- A single stronger finite order and smaller positive strip suffice for
all clauses of N09, with the original canonical control and state inverses. -/
theorem coupled_exists_N09Properties
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hchart : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CircleSpace S =>
        R.chartIncrement (liftSectorParameter S C z.1) z.2)) :
    ∃ base' : ℕ, ∃ ε' q0 : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N09Properties D T S C R G B (coupledControlInverse S B G)
        (coupledRecoveredInverseData hT hS h1 h2 h8) base' ε' q0 := by
  have hNex := coupled_exists_sector_feedback_smallness hS h1.2.2.1 hG h8 h1.2.1
  let bN : ℕ := hNex.choose
  let eN : ℝ := hNex.choose_spec.choose
  let qN : ℝ := hNex.choose_spec.choose_spec.choose
  have hN := hNex.choose_spec.choose_spec.choose_spec
  have hRex := coupled_exists_feedback_regularizing_neighborhood h1.2.2.1 h8 h1.2.1
  let bR : ℕ := hRex.choose
  let eR : ℝ := hRex.choose_spec.choose
  have hR := hRex.choose_spec.choose_spec
  let ℓ : ℕ := hR.2.2.2.choose
  let s0 : ℕ := hR.2.2.2.choose_spec.choose
  let base' : ℕ := max bN bR
  let ε' : ℝ := min eN eR
  let q0 : ℝ := min qN ε'
  let U := sectorNeighborhood S base' ε' q0
  have hb : base ≤ base' := hN.1.trans (le_max_left _ _)
  have hε' : 0 < ε' := lt_min hN.2.1 hR.2.1
  have hεε : ε' ≤ ε := (min_le_left eN eR).trans hN.2.2.1
  have hqpos : 0 < q0 := lt_min hN.2.2.2.1 hε'
  have hqle : q0 ≤ ε' := min_le_right _ _
  have hUN : U ⊆ sectorNeighborhood S bN eN qN :=
    coupled_sectorNeighborhood_mono (le_max_left bN bR)
      (min_le_left eN eR) (min_le_left qN ε')
  have hUR : U ⊆ sectorNeighborhood S bR eR eR :=
    coupled_sectorNeighborhood_mono (le_max_right bN bR)
      (min_le_right eN eR) (hqle.trans (min_le_right eN eR))
  have hUold : U ⊆ sectorNeighborhood S base ε ε :=
    fun z hz => hN.2.2.2.2.2.1 (hUN hz)
  have hU : IsOpen U := coupled_sectorNeighborhood_isOpen S base' ε' q0
  have hsmall : ∀ z ∈ U,
      ‖z.2 • controlFeedback S B G (liftSectorParameter S C z)‖ < (1 / 2 : ℝ) :=
    fun z hz => hN.2.2.2.2.2.2 z (hUN hz)
  have hregular : ∀ s, s0 ≤ s → ∃ c : ℝ, 0 ≤ c ∧ ∀ z ∈ U, ∀ u : ControlBanach,
      (S.circle (3 / 4 : ℝ)).grading s
        (z.2 • B.heightRow (liftSectorParameter S C z)
          (controlHeightResponse S B G (liftSectorParameter S C z) u)) ≤
        c * (1 + pairGrading (sectorGrading S) realGrading (s + ℓ) z) * ‖u‖ := by
    intro s hs
    obtain ⟨c, hc, h⟩ := hR.2.2.2.choose_spec.choose_spec s hs
    exact ⟨c, hc, fun z hz u => h z (hUR hz) u⟩
  have hconstant := coupled_constantFeedbackInverse_tame_on
    hT hS h1 hG h8 hU hUold hsmall hregular
  have hchart' := smoothTameOn_mono hchart (hU.prod isOpen_univ)
    (Set.prod_mono hUold (subset_refl _))
  have hV := coupledRecoveredInverseData_smoothTameOn
    hT hS h1 h2 hG h8 hU hUold hsmall hconstant hchart'
  have hstate : coupledNeighborhood S C base' ε' q0 ⊆ stateNeighborhood S C base ε := by
    intro z hz
    exact coupled_stateNeighborhood_mono hb hεε ⟨hz.1, hz.2.trans_le hqle⟩
  exact ⟨base', ε', q0, hb, hε', hεε,
    coupled_n09Properties_on_subdomain hT hS h1 h2 h8 hqpos hqle hstate
      (coupled_feedback_smallness_of_sector h1.2.2.1 hsmall) hV⟩

end ContinuousFlexibility.Statements
