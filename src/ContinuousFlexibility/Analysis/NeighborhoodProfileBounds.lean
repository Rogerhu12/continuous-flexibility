import ContinuousFlexibility.Analysis.NeighborhoodStateBounds
import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform size of the actual exponential profile perturbation

The discrete material weights absorb every fixed control loss.  Combining
their cofinite decay with the finitely many remaining indices gives a uniform
operator bound for the actual disjoint control sum.  No relation between a
control interval and a reference cell is added to the nonlinear hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- A bounded change of cell index preserves the uniform absorption of a
fixed coefficient power by any positive material weight. -/
theorem materialSample_shifted_weight_bounded
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (cell : ℕ → ℕ)
    (hIndex : ∃ B : ℝ, 0 < B ∧ ∀ m,
      |(D.cellIndex (cell m) : ℝ) - D.cellIndex m| ≤ B)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ m,
      T.H (T.sample m) ^ γ * T.E0 (T.sample (cell m)) ^ A ≤ L := by
  classical
  obtain ⟨B, hB, hindex⟩ := hIndex
  obtain ⟨δ, K, hδ, hK, henv⟩ := materialSample_endpoint_weight_bound hT hD hγ A hB.le
  have hcell : Tendsto cell cofinite cofinite := controlCell_tendsto_cofinite hD cell hindex
  have hnear : ∀ᶠ m in cofinite, endpointDistance D (T.sample (cell m)) < δ :=
    ((materialSample_endpointDistance_tendsto_zero hT hD).comp hcell).eventually_lt_const hδ
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _, _, hsamp, _, _⟩ := hdata
  have hγ' : 0 < γ / 16 := div_pos hγ (by norm_num)
  obtain ⟨_, _, _, hleft, hright⟩ := hdecay 0 (γ / 16) hγ'
  have hweight : Tendsto (fun m => T.H (T.sample m) ^ (γ / 16)) cofinite (𝓝 0) := by
    apply materialSample_tendsto_zero_of_endpoint_limits hT hD
      (f := fun r => T.H r ^ (γ / 16))
    · simpa only [Real.rpow_zero, mul_one] using hleft
    · simpa only [Real.rpow_zero, mul_one] using hright
  have hsmall : ∀ᶠ m in cofinite, K * T.H (T.sample (cell m)) ^ (γ / 16) < 1 := by
    have hl := (hweight.comp hcell).const_mul K
    rw [mul_zero] at hl
    exact hl.eventually_lt_const zero_lt_one
  let w : ℕ → ℝ := fun m => T.H (T.sample m) ^ γ * T.E0 (T.sample (cell m)) ^ A
  have hsamples (m : ℕ) : T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hD.choose_spec.2.1 m
  have heventually : ∀ᶠ m in cofinite, w m ≤ 1 := by
    filter_upwards [hnear, hsmall] with m hmnear hmsmall
    have hi : |(D.cellIndex m : ℝ) - D.cellIndex (cell m)| ≤ B :=
      (abs_sub_comm _ _).trans_le (hindex m)
    exact (henv m (cell m) (T.sample (cell m)) (hsamples _) (hsamp _) hi hmnear).trans
      hmsmall.le
  have hfinite : {m | ¬w m ≤ 1}.Finite := eventually_cofinite.mp heventually
  let F : Finset ℕ := hfinite.toFinset
  have hw (m : ℕ) : 0 ≤ w m :=
    mul_nonneg (Real.rpow_nonneg (hT.2.1 _ (hsamples m)).2.1.le _)
      (Real.rpow_nonneg (hT.2.1 _ (hsamples (cell m))).2.2.1.le _)
  refine ⟨max 1 (∑ m ∈ F, w m), zero_le_one.trans (le_max_left _ _), ?_⟩
  intro m
  by_cases hm : m ∈ F
  · exact (Finset.single_le_sum (f := w) (fun j _ => hw j) hm).trans (le_max_right _ _)
  · have hm' : w m ≤ 1 := by
      by_contra hn
      exact hm (hfinite.mem_toFinset.mpr hn)
    exact hm'.trans (le_max_left _ _)

theorem neighborhoodStateGrading_controls_le (S : PhysicalSpacesData) (s : ℕ)
    (x : AnnularState S) :
    |x.2.1| ≤ stateGrading S s x ∧
      (S.circle (3 / 4 : ℝ)).grading s x.2.2.1 ≤ stateGrading S s x := by
  have hheight : 0 ≤ (S.height (3 / 4 : ℝ)).grading s x.1.1 + ‖x.1.2‖ :=
    add_nonneg (apply_nonneg ((S.height (3 / 4 : ℝ)).grading s) x.1.1)
      (norm_nonneg x.1.2)
  have hκ := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading s) x.2.2.1
  have hη := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading s) x.2.2.2
  have htail : ‖x.2.1‖ + ((S.circle (3 / 4 : ℝ)).grading s x.2.2.1 +
      (S.circle (3 / 4 : ℝ)).grading s x.2.2.2) ≤ stateGrading S s x :=
    (le_add_of_nonneg_left hheight).trans_eq (neighborhoodStateGrading_apply S s x).symm
  exact ⟨(Real.norm_eq_abs x.2.1).symm.trans_le
      ((le_add_of_nonneg_right (add_nonneg hκ hη)).trans htail),
    ((le_add_of_nonneg_right hη).trans
      (le_add_of_nonneg_left (norm_nonneg x.2.1))).trans htail⟩

/-- The mean estimate retains its explicit dependence on the input grading. -/
theorem stateKappa_grading_weight_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (s : ℕ) (x : AnnularState S) (m : ℕ) :
    |stateKappa S x m| ≤
      (((1 / Real.pi) * Real.sqrt Real.pi) * stateGrading S s x) *
        T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have hmodel := hS.2.1 (3 / 4 : ℝ)
  have hmember := hmodel.2.2.2.1 x.2.2.1
  have hH (j : ℕ) : 0 < T.H (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 j)).2.1
  have hb := circleMember_angularMean_bound hmember hH m
  have hnorm : circleNorm T (3 / 4 : ℝ) 0 ((S.circle (3 / 4 : ℝ)).decode x.2.2.1) ≤
      (S.circle (3 / 4 : ℝ)).grading s x.2.2.1 := by
    rw [← hmodel.2.2.2.2.2.2.2 x.2.2.1 0]
    exact ContinuousFlexibility.Analysis.norm_coordinate_le_graded _ _ (Nat.zero_le s) x.2.2.1
  have hstate := hnorm.trans (neighborhoodStateGrading_controls_le S s x).2
  have hconst : 0 ≤ (1 / Real.pi) * Real.sqrt Real.pi := by positivity
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstate hconst) (Real.rpow_pos_of_pos (hH m) _).le)

/-- The actual disjoint sum has a bound linear in any input grading. -/
theorem stateControlSum_grading_bound_of_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C)
    (hIndex : ∃ B : ℝ, 0 < B ∧ ∀ m,
      |(D.cellIndex (C.cell m) : ℝ) - D.cellIndex m| ≤ B)
    (hJet : ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
      |C.control m r| ≤ B * T.E0 (T.sample (C.cell m)) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℕ, ∀ x : AnnularState S, ∀ r ∈ Ioo D.a D.b,
      |stateControlSum C x r| ≤ K * stateGrading S s x := by
  obtain ⟨B, hB, hcontrol⟩ := hJet
  obtain ⟨L, hL, hweight⟩ := materialSample_shifted_weight_bounded hT hD C.cell hIndex
    (show 0 < (3 / 4 : ℝ) by norm_num) B
  let P : ℝ := (1 / Real.pi) * Real.sqrt Real.pi
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨(P * B) * L, mul_nonneg (mul_nonneg hP hB.le) hL, ?_⟩
  intro s x r hr
  have hsize : 0 ≤ stateGrading S s x := apply_nonneg _ _
  have hterm (m : ℕ) (hm : r ∈ Ioo (C.left m) (C.right m)) :
      |stateKappa S x m * iteratedDeriv 0 (C.control m) r| ≤
        ((P * B) * L) * stateGrading S s x := by
    rw [iteratedDeriv_zero, abs_mul]
    have hκ := stateKappa_grading_weight_bound hD hT hS s x m
    have hκnonneg : 0 ≤ (P * stateGrading S s x) * T.H (T.sample m) ^ (3 / 4 : ℝ) :=
      (abs_nonneg _).trans hκ
    calc
      _ ≤ ((P * stateGrading S s x) * T.H (T.sample m) ^ (3 / 4 : ℝ)) *
          (B * T.E0 (T.sample (C.cell m)) ^ B) :=
        mul_le_mul hκ (hcontrol m r hm) (abs_nonneg _) hκnonneg
      _ = ((P * B) * stateGrading S s x) *
          (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B) := by ring
      _ ≤ ((P * B) * stateGrading S s x) * L :=
        mul_le_mul_of_nonneg_left (hweight m) (mul_nonneg (mul_nonneg hP hB.le) hsize)
      _ = _ := by ring
  simpa only [iteratedDeriv_zero] using abs_iteratedDeriv_stateControlSum_le hC x 0 hr
    (mul_nonneg (mul_nonneg (mul_nonneg hP hB.le) hL) hsize) hterm

/-- The actual exponential state profile is comparable to the reference on
one order-four neighbourhood; its radius is independent of later jet orders. -/
theorem exists_stateNeighborhood_profile_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (hborder : RadialTrueBorder D)
    (hC : controlGeometryConditions D S C)
    (hIndex : ∃ B : ℝ, 0 < B ∧ ∀ m,
      |(D.cellIndex (C.cell m) : ℝ) - D.cellIndex m| ≤ B)
    (hJets : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
        |iteratedDeriv s (C.control m) r| ≤ B * T.E0 (T.sample (C.cell m)) ^ B) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ z ∈ stateNeighborhood S C 4 ε,
      ∀ r ∈ Ioo D.a D.b,
        (1 / 2 : ℝ) ≤ stateProfile D S C z.1 r / D.w r ∧
        stateProfile D S C z.1 r / D.w r ≤ 2 := by
  have hJet : ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
      |C.control m r| ≤ B * T.E0 (T.sample (C.cell m)) ^ B := by
    simpa only [iteratedDeriv_zero] using hJets 0
  obtain ⟨K, hK, hcontrol⟩ := stateControlSum_grading_bound_of_bounds hD hT hS hC hIndex hJet
  obtain ⟨B₀, hB₀⟩ := hborder.1.continuous.bounded_above_of_compact_support hborder.2.1
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hχ (r : ℝ) : |D.chi r| ≤ B := by
    have hh : |D.chi r| ≤ B₀ := by simpa only [Real.norm_eq_abs] using hB₀ r
    exact hh.trans (le_max_left _ _)
  let L : ℝ := B + K
  have hL : 0 ≤ L := add_nonneg hB hK
  have hLone : 0 < L + 1 := by linarith only [hL]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε : ℝ := min (1 / 2) (Real.log 2 / (L + 1))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hlog hLone)
  have hεone : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hsmall : L * ε ≤ Real.log 2 := by
    have hh := (le_div_iff₀ hLone).mp (min_le_right (1 / 2) (Real.log 2 / (L + 1)))
    change ε * (L + 1) ≤ Real.log 2 at hh
    nlinarith only [hh, hε.le]
  have hνzero : C.referenceState.2.1 = 0 := href.2.2.1
  have hκzero : C.referenceState.2.2.1 = 0 := href.2.2.2.1
  refine ⟨ε, hε, hεone, ?_⟩
  intro z hz r hr
  let y : AnnularState S := z.1 - C.referenceState
  have hy : stateGrading S 4 y < ε := hz.1
  have hν : |z.1.2.1| ≤ stateGrading S 4 y := by
    simpa only [y, Prod.fst_sub, Prod.snd_sub, hνzero, sub_zero] using
      (neighborhoodStateGrading_controls_le S 4 y).1
  have heq : stateControlSum C y = stateControlSum C z.1 := by
    funext t
    simp only [stateControlSum, stateKappa, y, Prod.fst_sub, Prod.snd_sub, hκzero, sub_zero]
  have hsum : |stateControlSum C z.1 r| ≤ K * stateGrading S 4 y := by
    rw [← heq]
    exact hcontrol 4 y r hr
  let f : ℝ := z.1.2.1 * D.chi r + stateControlSum C z.1 r
  have hf : |f| ≤ Real.log 2 := by
    calc
      |f| ≤ |z.1.2.1 * D.chi r| + |stateControlSum C z.1 r| := abs_add_le _ _
      _ ≤ stateGrading S 4 y * B + K * stateGrading S 4 y := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hν (hχ r) (abs_nonneg _) (apply_nonneg _ _)) hsum
      _ = L * stateGrading S 4 y := by dsimp [L]; ring
      _ ≤ L * ε := mul_le_mul_of_nonneg_left hy.le hL
      _ ≤ Real.log 2 := hsmall
  have hw : 0 < D.w r := hD.choose_spec.1.2.2.2.2.1 r hr
  have hratio : stateProfile D S C z.1 r / D.w r = Real.exp f := by
    change D.w r * Real.exp f / D.w r = Real.exp f
    exact mul_div_cancel_left₀ _ hw.ne'
  rw [hratio]
  constructor
  · have hh := Real.exp_le_exp.mpr (abs_le.mp hf).1
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      one_div] using hh
  · exact (Real.exp_le_exp.mpr (abs_le.mp hf).2).trans_eq (Real.exp_log (by norm_num))

end ContinuousFlexibility.Statements
