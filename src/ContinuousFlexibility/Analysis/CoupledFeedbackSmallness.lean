import ContinuousFlexibility.Analysis.CoupledControlCircleDerivative
import ContinuousFlexibility.Analysis.CoupledControlNorms
import ContinuousFlexibility.Analysis.CoupledControlResponseSmooth
import ContinuousFlexibility.Analysis.CoupledSmoothParameterSmallness

/-!
# Uniform smallness of the actual control feedback

The scaled height row is the genuine height derivative of the circle
residual. Composing it with the scalar response gives a smooth linear
family which vanishes at parameter zero. Its true parameter derivative
therefore yields one finite-order neighborhood where its Banach norm is
less than one quarter. The stored diagonal inverse has norm at most two.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Function ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

/-- The feedback before the uniformly bounded diagonal inverse. -/
def coupledScaledMeanResponse (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (B : ControlColumnData S) (G : ScalarInverseData S)
    (z : StateDirections S × ℝ) : ControlBanach →L[ℝ] ControlBanach :=
  B.restriction.comp ((z.2 • B.heightRow (liftSectorParameter S C z)).comp
    (controlHeightResponse S B G (liftSectorParameter S C z)))

theorem coupledScaledMeanResponse_apply (z : StateDirections S × ℝ) (u : ControlBanach) :
    coupledScaledMeanResponse S C B G z u =
      B.restriction (z.2 • B.heightRow (liftSectorParameter S C z)
        (controlHeightResponse S B G (liftSectorParameter S C z) u)) := by
  simp only [coupledScaledMeanResponse, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply]

theorem coupledScaledMeanResponse_zero (x : StateDirections S) (u : ControlBanach) :
    coupledScaledMeanResponse S C B G (x, 0) u = 0 := by
  simp only [coupledScaledMeanResponse_apply, zero_smul, map_zero]

theorem coupledScaledMeanResponse_factorization (z : StateDirections S × ℝ) :
    z.2 • controlFeedback S B G (liftSectorParameter S C z) =
      (B.JInverse (liftSectorParameter S C z)).comp
        (coupledScaledMeanResponse S C B G z) := by
  ext u
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    controlFeedback_apply, controlMeanRow_apply, coupledScaledMeanResponse_apply, map_smul]

/-- Smoothness is proved for the scaled row on its original domain,
including the parameter value zero. -/
theorem coupledScaledMeanResponse_smoothTameOn
    (hS : IsPhysicalSpaces D T S)
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
      controlGrading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach =>
        coupledScaledMeanResponse S C B G z.1 z.2) := by
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) :=
    pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := tamePairGrading_monotone
    (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have htp : WithSeminorms p := withSeminorms_pairGrading
    (solve_sectorGrading_withSeminorms S) weighted_realGrading_withSeminorms
  have hpc : Monotone (pairGrading p controlGrading) :=
    tamePairGrading_monotone hp coupled_controlGrading_monotone
  have htpc : WithSeminorms (pairGrading p controlGrading) :=
    withSeminorms_pairGrading htp coupled_controlGrading_withSeminorms
  have htph : WithSeminorms (pairGrading p (heightPairGrading S)) :=
    withSeminorms_pairGrading htp (coupled_heightPairGrading_withSeminorms S)
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × HeightPair S) :=
    htph.toLocallyConvexSpace
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.2.1 (3 / 4 : ℝ)).2.1 n).isComplete.completeSpace_coe
  have hU : IsOpen (sectorNeighborhood S base ε ε) := h8.2.1
  have hcolumn := h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hresponse := coupled_controlHeightResponse_smoothTameOn hS hU hcolumn hG.2.2.2
  have hfst : SmoothTameOn (pairGrading p controlGrading) p
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × ControlBanach => z.1) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) ControlBanach)
      (scalar_pair_fst_isTame p controlGrading)
  have hin := smoothTameOn_prodMk_generic hpc htpc hfst hresponse
  have hrow := coupled_scaledHeightRow_smoothTameOn hRef h8
  have hc := smoothTameOn_comp_generic hpc htpc htph hin hrow
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  obtain ⟨b, hb⟩ := controlRestriction_isTame B
  have hout := smoothTameOn_continuousLinear B.restriction hb
  have hall := coupled_smoothTameOn_comp_banach hpc htpc
    (withSeminorms_graded _ _) hc hout (fun _ _ => mem_univ _)
  apply smoothTameOn_congr hall
  intro z hz
  simp only [Function.comp_def, coupledScaledMeanResponse_apply]

/-- The second Neumann hypothesis follows from the actual N08 smooth
family on one common stronger sector neighborhood. -/
theorem coupled_exists_sector_feedback_smallness
    (hS : IsPhysicalSpaces D T S)
    (hRef : referenceStateConditions D S C)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hε : 0 < ε) :
    ∃ base' : ℕ, ∃ ε' q0 : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ 0 < q0 ∧ q0 ≤ ε' ∧
      sectorNeighborhood S base' ε' q0 ⊆ sectorNeighborhood S base ε ε ∧
      ∀ z ∈ sectorNeighborhood S base' ε' q0,
        ‖z.2 • controlFeedback S B G (liftSectorParameter S C z)‖ < (1 / 2 : ℝ) := by
  have hsmooth := coupledScaledMeanResponse_smoothTameOn hS hRef hG h8
  obtain ⟨J, hJ⟩ := hsmooth
  have hzero : ((0 : StateDirections S), (0 : ℝ)) ∈
      sectorNeighborhood S base ε ε := by
    constructor
    · simpa only [map_zero] using hε
    · simpa only [abs_zero] using hε
  obtain ⟨W, hW, δ, hδ, hstrip⟩ :=
    coupled_exists_small_smooth_parameter_family h8.2.1 J hzero
      (fun x hx u => coupledScaledMeanResponse_zero x u)
  obtain ⟨b, ρ, hρ, hball⟩ := exists_seminormBall_subset_nhds
    (solve_sectorGrading_monotone S) (solve_sectorGrading_withSeminorms S) hW
  let ε' : ℝ := min ε ρ
  let q0 : ℝ := min ε' δ
  have hε' : 0 < ε' := lt_min hε hρ
  have hq0 : 0 < q0 := lt_min hε' hδ
  have hWmem (z : StateDirections S × ℝ)
      (hz : z ∈ sectorNeighborhood S (max base b) ε' q0) : z.1 ∈ W := by
    apply hball z.1
    rw [sub_zero]
    exact (solve_sectorGrading_monotone S (le_max_right base b) z.1).trans_lt
      (hz.1.trans_le (min_le_right ε ρ))
  have hsmall (z : StateDirections S × ℝ)
      (hz : z ∈ sectorNeighborhood S (max base b) ε' q0) :
      z ∈ sectorNeighborhood S base ε ε ∧
        ‖coupledScaledMeanResponse S C B G z‖ < (1 / 4 : ℝ) :=
    hstrip z.1 (hWmem z hz) z.2 (hz.2.trans_le (min_le_right ε' δ))
  refine ⟨max base b, ε', q0, le_max_left _ _, hε', min_le_left _ _, hq0,
    min_le_left _ _, (fun z hz => (hsmall z hz).1), ?_⟩
  intro z hz
  have hzold := (hsmall z hz).1
  have hA := (hsmall z hz).2
  have hzstate := liftSectorParameter_mem_stateNeighborhood (C := C) hzold le_rfl
  have hzsector := hRef.liftSectorParameter_sector z
  have hdiag : ∀ (u : ControlBanach) (m : ℕ),
      B.J (liftSectorParameter S C z) u m =
        B.diagonal (liftSectorParameter S C z) m * u m :=
    h8.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hzstate hzsector
  have hJinv : ∀ u : ControlBanach,
      B.J (liftSectorParameter S C z) (B.JInverse (liftSectorParameter S C z) u) = u :=
    fun u => (h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hzstate hzsector u).2
  have hlo : ∀ m : ℕ, (1 / 2 : ℝ) ≤ |B.diagonal (liftSectorParameter S C z) m| :=
    fun m => (h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hzstate hzsector m).1
  have hJ : ‖B.JInverse (liftSectorParameter S C z)‖ ≤ 2 :=
    controlJInverse_norm_le_two B _ hdiag hJinv hlo
  rw [coupledScaledMeanResponse_factorization]
  calc
    ‖(B.JInverse (liftSectorParameter S C z)).comp
        (coupledScaledMeanResponse S C B G z)‖ ≤
        ‖B.JInverse (liftSectorParameter S C z)‖ *
          ‖coupledScaledMeanResponse S C B G z‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * ‖coupledScaledMeanResponse S C B G z‖ :=
      mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
    _ < 2 * (1 / 4 : ℝ) := mul_lt_mul_of_pos_left hA (by norm_num)
    _ = (1 / 2 : ℝ) := by norm_num

end ContinuousFlexibility.Statements
