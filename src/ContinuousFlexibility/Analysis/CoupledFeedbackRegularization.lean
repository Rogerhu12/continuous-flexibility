import ContinuousFlexibility.Analysis.CoupledControlCircleDerivative
import ContinuousFlexibility.Analysis.CoupledControlAlgebra
import ContinuousFlexibility.Analysis.CoupledNeighborhoodRestriction
import ContinuousFlexibility.Analysis.CoupledRegularizingEstimates

/-!
# The actual feedback gains every circle order

The N08 control response is smoothing from its one control Banach space.
Its composition with the actual scaled height row therefore has a fixed
loss estimate in the original circle grading, on one common smaller
neighborhood. This estimate supplies the regularity of the recovered
constant control without assigning higher circle orders to arbitrary
elements of the base control space.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

theorem coupled_controlHeightResponse_grading_bound
    (h8 : N08Properties D T S C R G P B base loss ε) :
    ∀ s, ∃ c : ℝ, 0 ≤ c ∧ ∀ z ∈ stateNeighborhood S C base ε, ∀ u,
      heightPairGrading S s (controlHeightResponse S B G z u) ≤
        c * (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|) * ‖u‖ := by
  have h := h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro s
  obtain ⟨c, hc, h⟩ := h s
  refine ⟨c, hc.le, fun z hz u => ?_⟩
  rw [controlHeightResponse_apply]
  have hb := h z hz u
  have hs := apply_nonneg (S.sourceGrading s) (B.heightColumn z u)
  have hn := abs_nonneg (G.G z (B.heightColumn z u)).2
  linarith only [hb, hs, hn]

/-- A fixed-loss circle estimate for the actual scaled height feedback.
The radius and input order are chosen before all output orders. -/
theorem coupled_exists_feedback_regularizing_neighborhood
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε) (hε : 0 < ε) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∃ loss' b : ℕ, ∀ s, b ≤ s → ∃ c : ℝ, 0 ≤ c ∧
        ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ u : ControlBanach,
          (S.circle (3 / 4 : ℝ)).grading s
            (z.2 • B.heightRow (liftSectorParameter S C z)
              (controlHeightResponse S B G (liftSectorParameter S C z) u)) ≤
            c * (1 + pairGrading (sectorGrading S) realGrading (s + loss') z) * ‖u‖ := by
  let p := pairGrading (sectorGrading S) realGrading
  let A : (StateDirections S × ℝ) → HeightPair S →L[ℝ] CircleSpace S :=
    fun z => z.2 • B.heightRow (liftSectorParameter S C z)
  have hA : SmoothTameOn (pairGrading p (heightPairGrading S))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S => A z.1 z.2) := by
    simpa only [A, ContinuousLinearMap.smul_apply] using
      coupled_scaledHeightRow_smoothTameOn hRef h8
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε := by
    change sectorGrading S base 0 < ε ∧ |(0 : ℝ)| < ε
    simpa only [map_zero, abs_zero] using And.intro hε hε
  obtain ⟨bNear, δ, hδ, lA, bA, hA⟩ := coupled_uniformLinearFamilyTame_near hA hzero
  let base' := max base (max bNear (bA + loss))
  let ε' := min ε (min 1 (δ / 4))
  have hb : base ≤ base' := le_max_left _ _
  have hbNear : bNear ≤ base' := (le_max_left _ _).trans (le_max_right _ _)
  have hbLow : bA + loss ≤ base' := (le_max_right _ _).trans (le_max_right _ _)
  have hε' : 0 < ε' := lt_min hε (lt_min zero_lt_one (by positivity))
  have hεε : ε' ≤ ε := min_le_left _ _
  have hεone : ε' ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεδ : ε' ≤ δ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hp : Monotone p := pairGrading_monotone
    (solve_sectorGrading_monotone S) (fun _ _ _ _ => le_rfl)
  have hmem {z : StateDirections S × ℝ}
      (hz : z ∈ sectorNeighborhood S base' ε' ε') :
      z ∈ sectorNeighborhood S base ε ε ∧ p bNear (z - 0) < δ := by
    refine ⟨coupled_sectorNeighborhood_mono hb hεε hεε hz, ?_⟩
    have hd := (solve_sectorGrading_monotone S hbNear z.1).trans_lt hz.1
    change p bNear (z - 0) < δ
    rw [sub_zero]
    change sectorGrading S bNear z.1 + ‖z.2‖ < δ
    rw [Real.norm_eq_abs]
    linarith only [hd, hz.2, hεδ, hδ]
  have hrow : ∀ s, bA ≤ s → ∃ c : ℝ, 0 ≤ c ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ η,
      (S.circle (3 / 4 : ℝ)).grading s (A z η) ≤
        c * (heightPairGrading S (s + lA) η +
          (1 + p (s + lA) z) * heightPairGrading S bA η) := by
    intro s hs
    obtain ⟨c, hc, h⟩ := hA s hs
    exact ⟨c, hc, fun z hz => h z (hmem hz)⟩
  have hresponse : ∀ s, ∃ c : ℝ, 0 ≤ c ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ u,
      heightPairGrading S s (controlHeightResponse S B G (liftSectorParameter S C z) u) ≤
        c * (1 + p (s + loss) z) * ‖u‖ := by
    intro s
    obtain ⟨c, hc, h⟩ := coupled_controlHeightResponse_grading_bound h8 s
    refine ⟨c, hc, fun z hz u => ?_⟩
    have hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε := by
      exact liftSectorParameter_mem_stateNeighborhood (hmem hz).1 le_rfl
    have ht := h (liftSectorParameter S C z) hz' u
    simpa only [liftSectorParameter, add_sub_cancel_left, p, pairGrading_apply,
      sectorGrading, Seminorm.comp_apply, Submodule.subtype_apply, realGrading,
      coe_normSeminorm, Real.norm_eq_abs, add_assoc] using ht
  have hlow : ∀ z ∈ sectorNeighborhood S base' ε' ε', p (bA + loss) z ≤ 2 := by
    intro z hz
    have hd := (solve_sectorGrading_monotone S hbLow z.1).trans_lt hz.1
    change sectorGrading S (bA + loss) z.1 + ‖z.2‖ ≤ 2
    rw [Real.norm_eq_abs]
    linarith only [hd, hz.2, hεone]
  refine ⟨base', ε', hb, hε', hεε, lA + loss, bA, ?_⟩
  exact coupled_regularizing_composition_bound hp
    (A := fun z => (A z).toLinearMap)
    (H := fun z => (controlHeightResponse S B G (liftSectorParameter S C z)).toLinearMap)
    (by norm_num : (0 : ℝ) ≤ 2) hrow hresponse hlow

end ContinuousFlexibility.Statements
