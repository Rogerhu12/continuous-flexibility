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
set_option backward.isDefEq.respectTransparency.types false

private theorem coupled_regularizing_middle_le
    {a b c d : ℝ} (h : a + b + c ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) : b ≤ d := by
  linarith only [h, ha, hc]

private theorem coupled_regularizing_near_size
    {a b ε δ : ℝ} (ha : a < ε) (hb : b < ε) (he : ε ≤ δ / 4)
    (hd : 0 < δ) : a + b < δ := by
  linarith only [ha, hb, he, hd]

private theorem coupled_regularizing_small_size_le_two
    {a b ε : ℝ} (ha : a < ε) (hb : b < ε) (he : ε ≤ 1) : a + b ≤ 2 := by
  linarith only [ha, hb, he]

section ParameterAlgebra

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

private theorem coupled_regularizing_zero_small
    (q : ℕ → Seminorm ℝ E) (b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    q b (0 : E) < ε ∧ |(0 : ℝ)| < ε := by
  simpa only [map_zero, abs_zero] using And.intro hε hε

private theorem coupled_regularizing_pair_value
    (q : ℕ → Seminorm ℝ E) (n : ℕ) (z : E × ℝ) :
    pairGrading q realGrading n z = q n z.1 + |z.2| := by
  exact (ContinuousFlexibility.Analysis.pairGrading_apply q realGrading n z).trans
    (congrArg (fun x : ℝ => q n z.1 + x) (Real.norm_eq_abs z.2))

private theorem coupled_regularizing_pair_sub_zero
    (q : ℕ → Seminorm ℝ E) (n : ℕ) (z : E × ℝ) :
    pairGrading q realGrading n (z - 0) = q n z.1 + |z.2| := by
  rw [sub_zero, coupled_regularizing_pair_value]

private theorem coupled_regularizing_affine_size
    (q : ℕ → Seminorm ℝ E) (W : Submodule ℝ E) (x0 : E) (n : ℕ) (z : W × ℝ) :
    1 + q n (x0 + z.1.val - x0) + |z.2| =
      1 + pairGrading (fun n => (q n).comp W.subtype) realGrading n z := by
  simp only [add_sub_cancel_left, coupled_regularizing_pair_value,
    Seminorm.comp_apply, Submodule.subtype_apply, add_assoc]

end ParameterAlgebra

private def coupled_regularizing_scaledRow
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [ContinuousSMul ℝ F]
    (a : ℝ) (L : E →L[ℝ] F) : E →L[ℝ] F := a • L

private theorem coupled_regularizing_scaledRow_apply
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [ContinuousSMul ℝ F]
    (a : ℝ) (L : E →L[ℝ] F) (v : E) :
    coupled_regularizing_scaledRow a L v = a • L v :=
  _root_.smul_apply L a v

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

theorem coupled_controlHeightResponse_grading_bound
    (h8 : N08Properties D T S C R G P B base loss ε) :
    ∀ s, ∃ c : ℝ, 0 ≤ c ∧ ∀ z ∈ stateNeighborhood S C base ε, ∀ u,
      heightPairGrading S s (controlHeightResponse S B G z u) ≤
        c * (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|) * ‖u‖ := by
  intro s
  let hbound := h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s
  let c : ℝ := hbound.choose
  refine ⟨c, hbound.choose_spec.1.le, fun z hz u => ?_⟩
  have hb := hbound.choose_spec.2 z hz u
  have hs := apply_nonneg (S.sourceGrading s) (B.heightColumn z u)
  have hn := abs_nonneg (G.G z (B.heightColumn z u)).2
  exact (congrArg (heightPairGrading S s) (controlHeightResponse_apply B G z u)).trans_le
    (coupled_regularizing_middle_le hb hs hn)

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
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) := pairGrading (sectorGrading S) realGrading
  let A : (StateDirections S × ℝ) → HeightPair S →L[ℝ] CircleSpace S :=
    fun z => coupled_regularizing_scaledRow z.2 (B.heightRow (liftSectorParameter S C z))
  have hA : SmoothTameOn (pairGrading p (heightPairGrading S))
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S => A z.1 z.2) := by
    exact smoothTameOn_congr (coupled_scaledHeightRow_smoothTameOn hRef h8)
      (fun z _ => (coupled_regularizing_scaledRow_apply z.1.2
        (B.heightRow (liftSectorParameter S C z.1)) z.2).symm)
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε :=
    coupled_regularizing_zero_small (sectorGrading S) base hε
  let hnear := coupled_uniformLinearFamilyTame_near hA hzero
  let bNear : ℕ := hnear.choose
  let δ : ℝ := hnear.choose_spec.choose
  have hδ : 0 < δ := hnear.choose_spec.choose_spec.1
  let hfamily := hnear.choose_spec.choose_spec.2
  let lA : ℕ := hfamily.choose
  let bA : ℕ := hfamily.choose_spec.choose
  have hABound := hfamily.choose_spec.choose_spec
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
    exact (coupled_regularizing_pair_sub_zero (sectorGrading S) bNear z).trans_lt
      (coupled_regularizing_near_size hd hz.2 hεδ hδ)
  have hrow : ∀ s, bA ≤ s → ∃ c : ℝ, 0 ≤ c ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ η,
      (S.circle (3 / 4 : ℝ)).grading s (A z η) ≤
        c * (heightPairGrading S (s + lA) η +
          (1 + p (s + lA) z) * heightPairGrading S bA η) := by
    intro s hs
    let hbound := hABound s hs
    exact ⟨hbound.choose, hbound.choose_spec.1,
      fun z hz η => hbound.choose_spec.2 z (hmem hz) η⟩
  have hresponse : ∀ s, ∃ c : ℝ, 0 ≤ c ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ u,
      heightPairGrading S s (controlHeightResponse S B G (liftSectorParameter S C z) u) ≤
        c * (1 + p (s + loss) z) * ‖u‖ := by
    intro s
    let hbound := coupled_controlHeightResponse_grading_bound h8 s
    let c : ℝ := hbound.choose
    refine ⟨c, hbound.choose_spec.1, fun z hz u => ?_⟩
    have hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε := by
      exact liftSectorParameter_mem_stateNeighborhood (hmem hz).1 le_rfl
    have ht := hbound.choose_spec.2 (liftSectorParameter S C z) hz' u
    exact ht.trans_eq (congrArg (fun a : ℝ => c * a * ‖u‖)
      (coupled_regularizing_affine_size (stateGrading S) (stateSectorSubmodule S)
        C.referenceState (s + loss) z))
  have hlow : ∀ z ∈ sectorNeighborhood S base' ε' ε', p (bA + loss) z ≤ 2 := by
    intro z hz
    have hd := (solve_sectorGrading_monotone S hbLow z.1).trans_lt hz.1
    exact (coupled_regularizing_pair_value (sectorGrading S) (bA + loss) z).trans_le
      (coupled_regularizing_small_size_le_two hd hz.2 hεone)
  refine ⟨base', ε', hb, hε', hεε, lA + loss, bA, ?_⟩
  exact coupled_regularizing_composition_bound hp
    (A := fun z => (A z).toLinearMap)
    (H := fun z => (controlHeightResponse S B G (liftSectorParameter S C z)).toLinearMap)
    (by norm_num : (0 : ℝ) ≤ 2) hrow hresponse hlow

end ContinuousFlexibility.Statements
