import ContinuousFlexibility.Analysis.CoupledControlCircleDerivative
import ContinuousFlexibility.Analysis.CoupledControlNorms
import ContinuousFlexibility.Analysis.CoupledControlResponseSmooth
import ContinuousFlexibility.Analysis.CoupledSmoothParameterSmallness
import ContinuousFlexibility.Analysis.CoupledConstantFeedbackSmooth

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

private theorem coupled_map_zero_scale
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) (v : E) :
    L ((0 : ℝ) • v) = 0 := by
  rw [zero_smul, L.map_zero]

private theorem coupled_seminorm_zero_lt
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) {ε : ℝ} (hε : 0 < ε) : p 0 < ε := by
  simpa only [map_zero] using hε

private theorem coupled_restrict_smooth_family
    {X Y : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    {U : Set X} {f : X → Y} (hf : SmoothTameOn p q U f)
    (L : Y →L[ℝ] ControlBanach)
    (hL : ∃ b : ℕ, IsTameLinear q controlGrading L.toLinearMap 0 b) :
    SmoothTameOn p controlGrading U (fun x => L (f x)) := by
  letI : LocallyConvexSpace ℝ Y := htq.toLocallyConvexSpace
  obtain ⟨b, hb⟩ := hL
  exact coupled_smoothTameOn_comp_banach hp htp htq hf
    (smoothTameOn_continuousLinear L hb) (fun _ _ => mem_univ _)

private theorem coupled_smallness_on_seminorm_box
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) (htp : WithSeminorms p)
    {U : Set (X × ℝ)} {A : X × ℝ → ControlBanach →L[ℝ] ControlBanach}
    (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ univ) (fun z : (X × ℝ) × ControlBanach => A z.1 z.2))
    (h0 : ((0 : X), (0 : ℝ)) ∈ U)
    (hzero : ∀ x, (x, 0) ∈ U → ∀ u, A (x, 0) u = 0)
    (base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℕ, ∃ ε' q0 : ℝ,
      base ≤ b ∧ 0 < ε' ∧ ε' ≤ ε ∧ 0 < q0 ∧ q0 ≤ ε' ∧
      ∀ z : X × ℝ, p b z.1 < ε' → |z.2| < q0 →
        z ∈ U ∧ ‖A z‖ < (1 / 4 : ℝ) := by
  obtain ⟨W, hW, δ, hδ, hstrip⟩ :=
    coupled_exists_small_smooth_parameter_family hU J h0 hzero
  obtain ⟨b, ρ, hρ, hball⟩ := exists_seminormBall_subset_nhds hp htp hW
  let ε' : ℝ := min ε ρ
  let q0 : ℝ := min ε' δ
  have hε' : 0 < ε' := lt_min hε hρ
  have hq0 : 0 < q0 := lt_min hε' hδ
  refine ⟨max base b, ε', q0, le_max_left _ _, hε', min_le_left _ _, hq0,
    min_le_left _ _, fun z hz hq => ?_⟩
  have hx : z.1 ∈ W := hball z.1 (by
    rw [sub_zero]
    exact (hp (le_max_right base b) z.1).trans_lt (hz.trans_le (min_le_right ε ρ)))
  exact hstrip z.1 hx z.2 (hq.trans_le (min_le_right ε' δ))

private theorem coupled_norm_comp_lt_half
    (J A : ControlBanach →L[ℝ] ControlBanach)
    (hJ : ‖J‖ ≤ 2) (hA : ‖A‖ < (1 / 4 : ℝ)) :
    ‖J.comp A‖ < (1 / 2 : ℝ) := by
  calc
    ‖J.comp A‖ ≤ ‖J‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * ‖A‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
    _ < 2 * (1 / 4 : ℝ) := mul_lt_mul_of_pos_left hA (by norm_num)
    _ = (1 / 2 : ℝ) := by norm_num

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
        (controlHeightResponse S B G (liftSectorParameter S C z) u)) := rfl

theorem coupledScaledMeanResponse_zero (x : StateDirections S) (u : ControlBanach) :
    coupledScaledMeanResponse S C B G (x, 0) u = 0 := by
  exact (coupledScaledMeanResponse_apply (x, 0) u).trans
    (coupled_map_zero_scale B.restriction.toLinearMap _)

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
  have hall := coupled_restrict_smooth_family
    (tamePairGrading_monotone
      (tamePairGrading_monotone (solve_sectorGrading_monotone S) weighted_realGrading_monotone)
      coupled_controlGrading_monotone)
    (withSeminorms_pairGrading
      (withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
        weighted_realGrading_withSeminorms) coupled_controlGrading_withSeminorms)
    (withSeminorms_graded _ _)
    (coupled_scaledHeightControlResponse_smoothTameOn hS hRef hG h8)
    B.restriction (controlRestriction_isTame B)
  apply smoothTameOn_congr hall
  intro z hz
  exact (coupledScaledMeanResponse_apply z.1 z.2).symm

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
  have hzero : ((0 : StateDirections S), (0 : ℝ)) ∈
      sectorNeighborhood S base ε ε :=
    ⟨coupled_seminorm_zero_lt (sectorGrading S base) hε, abs_zero.trans_lt hε⟩
  have hexists := coupled_smallness_on_seminorm_box
    (solve_sectorGrading_monotone S) (solve_sectorGrading_withSeminorms S)
    h8.2.1 hsmooth.choose hzero (fun x hx u => coupledScaledMeanResponse_zero x u) base hε
  let b : ℕ := hexists.choose
  let ε' : ℝ := hexists.choose_spec.choose
  let q0 : ℝ := hexists.choose_spec.choose_spec.choose
  have hb : base ≤ b := hexists.choose_spec.choose_spec.choose_spec.1
  have hε' : 0 < ε' := hexists.choose_spec.choose_spec.choose_spec.2.1
  have he : ε' ≤ ε := hexists.choose_spec.choose_spec.choose_spec.2.2.1
  have hq : 0 < q0 := hexists.choose_spec.choose_spec.choose_spec.2.2.2.1
  have hqe : q0 ≤ ε' := hexists.choose_spec.choose_spec.choose_spec.2.2.2.2.1
  have hsmall (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S b ε' q0) :
      z ∈ sectorNeighborhood S base ε ε ∧
        ‖coupledScaledMeanResponse S C B G z‖ < (1 / 4 : ℝ) :=
    hexists.choose_spec.choose_spec.choose_spec.2.2.2.2.2 z hz.1 hz.2
  refine ⟨b, ε', q0, hb, hε', he, hq, hqe, (fun z hz => (hsmall z hz).1), ?_⟩
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
  exact (congrArg (fun A : ControlBanach →L[ℝ] ControlBanach => ‖A‖)
    (coupledScaledMeanResponse_factorization z)).trans_lt
      (coupled_norm_comp_lt_half _ _ hJ hA)

end ContinuousFlexibility.Statements
