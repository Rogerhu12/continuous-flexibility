import ContinuousFlexibility.Analysis.N08JetDifference
import ContinuousFlexibility.Analysis.N08CircleDiagonalContinuity

/-!
# A quantitative comparison of the actual control diagonal

N02 supplies the second jet of the same tower that defines the control
column. A scalar mean observation of that jet gives a Lipschitz estimate
for each diagonal entry, with only a fixed material-envelope power. The
order, radius and constant are chosen before the control label.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08ControlMeanCoordinate_bound (S : PhysicalSpacesData) (m s : ℕ)
    (u : CircleSpace S) :
    |n08ControlMeanCoordinate S m u| ≤
      n08ControlMeanConstant * (S.circle (3 / 4 : ℝ)).grading s u := by
  rw [n08ControlMeanCoordinate_apply]
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (n08ControlRestriction S u) m
  have hzero := n08ControlRestriction_norm_le S u
  have hgrade : (S.circle (3 / 4 : ℝ)).grading 0 u ≤
      (S.circle (3 / 4 : ℝ)).grading s u :=
    gradedSeminorm_monotone _ _ (Nat.zero_le s) u
  exact (by simpa only [Real.norm_eq_abs] using h).trans
    (hzero.trans (mul_le_mul_of_nonneg_left hgrade n08ControlMeanConstant_nonneg))

theorem n08CircleSectorPoint_val (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {x : AnnularState S}
    (hs : stateSector S x) (q : ℝ) :
    (n08CircleSectorPoint hS C (x, q)).1.val = x - C.referenceState :=
  n08_stateProjection_eq_self hS _ ((stateSectorSubmodule S).sub_mem hs href.stateSector)

theorem n08CircleSectorPoint_grading (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {x : AnnularState S}
    (hs : stateSector S x) (q : ℝ) (s : ℕ) :
    pairGrading (sectorGrading S) realGrading s (n08CircleSectorPoint hS C (x, q)) =
      stateGrading S s (x - C.referenceState) + |q| := by
  change stateGrading S s (n08CircleSectorPoint hS C (x, q)).1.val + ‖q‖ = _
  rw [n08CircleSectorPoint_val hS href hs, Real.norm_eq_abs]

private theorem n08_difference_after_center
    {E : Type*} [AddCommGroup E] (a x y : E) : (y - a) - (x - a) = y - x := by
  abel

theorem n08CircleSectorPoint_sub_grading (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {x y : AnnularState S}
    (hsx : stateSector S x) (hsy : stateSector S y) (q : ℝ) (s : ℕ) :
    pairGrading (sectorGrading S) realGrading s
      (n08CircleSectorPoint hS C (y, q) - n08CircleSectorPoint hS C (x, q)) =
      stateGrading S s (y - x) := by
  change stateGrading S s ((n08CircleSectorPoint hS C (y, q)).1.val -
      (n08CircleSectorPoint hS C (x, q)).1.val) + ‖q - q‖ = _
  rw [n08CircleSectorPoint_val hS href hsy, n08CircleSectorPoint_val hS href hsx,
    n08_difference_after_center, sub_self, norm_zero, add_zero]

def n08ControlSectorDirection (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    StateDirections S × ℝ :=
  (n08_sectorProjection hS (0, 0, n08ControlBasis hS m, 0), 0)

theorem n08ControlSectorDirection_grading (hS : IsPhysicalSpaces D T S) (m s : ℕ) :
    pairGrading (sectorGrading S) realGrading s (n08ControlSectorDirection hS m) =
      (S.circle (3 / 4 : ℝ)).grading s (n08ControlBasis hS m) := by
  change stateGrading S s
    (n08_stateProjection hS (0, 0, n08ControlBasis hS m, 0)) + ‖(0 : ℝ)‖ = _
  rw [n08_stateProjection_eq_self hS _ (n08ControlBasis_direction_sector hS m),
    norm_zero, add_zero, n08_controlDirection_grading]

theorem n08_sectorNeighborhood_convex (S : PhysicalSpacesData) (base : ℕ) (ε q0 : ℝ) :
    Convex ℝ (sectorNeighborhood S base ε q0) := by
  have h := ((sectorGrading S base).convex_ball 0 ε).prod
    ((normSeminorm ℝ ℝ).convex_ball 0 q0)
  convert h using 1
  ext z
  simp only [sectorNeighborhood, Set.mem_setOf_eq, Set.mem_prod, Seminorm.mem_ball_zero]
  rfl

/-- The genuine control diagonal is locally Lipschitz in the state with a
single polynomial material loss, uniformly over its label. -/
theorem n08CircleDiagonal_state_difference_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) :
    ∃ b : ℕ, ∃ δ K : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧ 0 ≤ K ∧
      ∀ x y : AnnularState S, ∀ q : ℝ,
        (x, q) ∈ stateNeighborhood S C b δ →
        (y, q) ∈ stateNeighborhood S C b δ →
        stateSector S x → stateSector S y → ∀ m,
        |n08CircleDiagonal hS hR (y, q) m - n08CircleDiagonal hS hR (x, q) m| ≤
          K * T.M (T.sample m) ^ b * stateGrading S b (y - x) := by
  let p := pairGrading (sectorGrading S) realGrading
  let J := n08CircleSectorJet hR
  have hp : Monotone p := pairGrading_monotone (solve_sectorGrading_monotone S)
    (fun _ _ _ _ => le_rfl)
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε := by
    constructor
    · simpa only [sub_self] using
        n08_seminorm_center_lt (sectorGrading S base) (0 : StateDirections S) hN.2.1
    · simpa only [abs_zero] using hN.2.1
  obtain ⟨l, a, ρ, hρ, hb⟩ := (n08_return_smoothTame hR).choose_spec 2 0 hzero
  obtain ⟨K, hK, hKb⟩ := hb a le_rfl
  let n := max a (a + l)
  let b := max base n
  let δ := min ε (min ρ 1) / 4
  have hδ : 0 < δ := div_pos (lt_min hN.2.1 (lt_min hρ zero_lt_one)) (by norm_num)
  have hδε : δ ≤ ε := by
    have h := min_le_left ε (min ρ 1)
    dsimp only [δ]
    linarith only [h, hN.2.1]
  have hδρ : 2 * δ < min ρ 1 := by
    have h := min_le_right ε (min ρ 1)
    have hr : 0 < min ρ 1 := lt_min hρ zero_lt_one
    dsimp only [δ]
    linarith only [h, hr]
  let Kout := n08ControlMeanConstant * (4 * K) * n08ControlBasisConstant n
  have hKout : 0 ≤ Kout := mul_nonneg
    (mul_nonneg n08ControlMeanConstant_nonneg (mul_nonneg (by norm_num) hK))
    (n08ControlBasisConstant_nonneg n)
  refine ⟨b, δ, Kout, le_max_left _ _, hδ, hδε, hKout, ?_⟩
  intro x y q hx hy hsx hsy m
  let X := n08CircleSectorPoint hS C (x, q)
  let Y := n08CircleSectorPoint hS C (y, q)
  let V := n08ControlSectorDirection hS m
  have hxyold : stateNeighborhood S C b δ ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono (le_max_left base n) hδε
  have hX : X ∈ sectorNeighborhood S base ε ε := by
    apply n08CircleSectorPoint_mem hS hN.2.2.1
    simpa only [n08_stateProjection_eq_self hS x hsx] using hxyold hx
  have hY : Y ∈ sectorNeighborhood S base ε ε := by
    apply n08CircleSectorPoint_mem hS hN.2.2.1
    simpa only [n08_stateProjection_eq_self hS y hsy] using hxyold hy
  have hsmallX : p n X < min ρ 1 := by
    rw [n08CircleSectorPoint_grading hS hN.2.2.1 hsx]
    have hg := solve_stateGrading_monotone S (le_max_right base n) (x - C.referenceState)
    exact (add_lt_add (hg.trans_lt hx.1) hx.2).trans
      (by simpa only [two_mul] using hδρ)
  have hsmallY : p n Y < min ρ 1 := by
    rw [n08CircleSectorPoint_grading hS hN.2.2.1 hsy]
    have hg := solve_stateGrading_monotone S (le_max_right base n) (y - C.referenceState)
    exact (add_lt_add (hg.trans_lt hy.1) hy.2).trans
      (by simpa only [two_mul] using hδρ)
  have hjet : ∀ z ∈ sectorNeighborhood S base ε ε, p a z < ρ → ∀ d v,
      (S.circle (3 / 4 : ℝ)).grading a
          (J.D 2 z (Fin.cons d (Fin.cons v Fin.elim0))) ≤
        K * oneHighVariationWeight p a (a + l) z (Fin.cons d (Fin.cons v Fin.elim0)) := by
    intro z hz hnear d v
    simpa only [sub_zero, oneHighVariationWeight] using
      hKb z hz (by simpa only [sub_zero] using hnear) (Fin.cons d (Fin.cons v Fin.elim0))
  have hdiff := n08_firstJet_tame_difference_bound J p hp
    ((S.circle (3 / 4 : ℝ)).grading a) hK hjet (n08ControlMeanCoordinate S m)
    n08ControlMeanConstant_nonneg (n08ControlMeanCoordinate_bound S m a)
    (v := V) hsmallX hsmallY
    (fun t ht => (n08_sectorNeighborhood_convex S base ε ε).add_smul_sub_mem hX hY ht)
  have hm := n08_material_sample_bounds hN.1.1 hT m
  have hV : p n V ≤ n08ControlBasisConstant n * T.M (T.sample m) ^ b := by
    rw [n08ControlSectorDirection_grading]
    exact (n08ControlBasis_grading_le hS m n hm.1 hm.2).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm.2 (le_max_right base n))
        (n08ControlBasisConstant_nonneg n))
  have hd : p n (Y - X) ≤ stateGrading S b (y - x) := by
    rw [n08CircleSectorPoint_sub_grading hS hN.2.2.1 hsx hsy]
    exact solve_stateGrading_monotone S (le_max_right base n) (y - x)
  have hn : 0 ≤ n08ControlMeanConstant * (4 * K) :=
    mul_nonneg n08ControlMeanConstant_nonneg (mul_nonneg (by norm_num) hK)
  have hfinal := hdiff.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hd hn) hV (apply_nonneg _ _)
    (mul_nonneg hn (apply_nonneg _ _)))
  rw [n08CircleDiagonal_value, n08CircleDiagonal_value]
  convert hfinal using 1 <;> dsimp only [Kout] <;> ring

end ContinuousFlexibility.Statements
